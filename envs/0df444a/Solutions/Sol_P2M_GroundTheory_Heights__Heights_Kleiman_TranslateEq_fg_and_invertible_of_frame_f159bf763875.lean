-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_fg_and_invertible_of_frame_f159bf763875
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:34.563191+00:00
-- url     : https://prove2.me/submissions/c90f9242-ddab-4fb1-b6df-375be7a534d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundleLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_of_forall_pow_mul_mem_e651439d42d9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open scoped Pointwise
variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
variable (A : Subalgebra S Ω) {k : ℕ} (f c : Fin k → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (L : Submodule A Ω) (b : Fin k → Ω)
    (hf : ∀ l, f l ∈ A) (hc : ∀ l, c l ∈ A) (hs : ∑ l, c l * f l = 1) (hb : ∀ l, b l ≠ 0)
    (hL : ∀ l e, (∃ n : ℕ, f l ^ n * e ∈ L) ↔ ∃ a : Ω, (∃ n : ℕ, f l ^ n * a ∈ A) ∧ e = a * b l) :
    L.FG ∧ ∃ L' : Submodule A Ω, L * L' = 1 := by
  have hgen : ∀ l, ∃ n : ℕ, f l ^ n * b l ∈ L := fun l =>
    (hL l (b l)).2 ⟨1, ⟨0, by rw [pow_zero, one_mul]; exact one_mem A⟩, (one_mul _).symm⟩
  choose n hn using hgen
  set g : Fin k → Ω := fun l => f l ^ n l * b l with hg
  have hloc : ∀ l, ∀ e ∈ L, ∃ a : Ω, (∃ m : ℕ, f l ^ m * a ∈ A) ∧ e = a * b l := fun l e he =>
    (hL l e).1 ⟨0, by rw [pow_zero, one_mul]; exact he⟩
  have hLG : L = Submodule.span A (Set.range g) := by
    apply le_antisymm
    · intro e he
      apply mem_of_forall_pow_mul_mem A f c hf hc hs
      intro l
      obtain ⟨a, ⟨m, hm⟩, rfl⟩ := hloc l e he
      refine ⟨m + n l, ?_⟩
      have : f l ^ (m + n l) * (a * b l) = (⟨f l ^ m * a, hm⟩ : A) • g l := by
        rw [Subalgebra.smul_def, smul_eq_mul, hg]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact hn l
  refine ⟨hLG ▸ Submodule.fg_span (Set.finite_range g), 1 / L, le_antisymm ?_ ?_⟩
  · rw [Submodule.mul_le]
    intro p hp q hq
    rw [mul_comm]
    exact (Submodule.mem_div_iff_forall_mul_mem.1 hq) p hp
  · rw [Submodule.one_le]
    apply mem_of_forall_pow_mul_mem A f c hf hc hs
    intro l
    have hbd : ∀ s, ∃ m : ℕ, f l ^ m * (g s / b l) ∈ A := by
      intro s
      obtain ⟨a, ⟨m, hm⟩, hgs⟩ := hloc l (g s) (hn s)
      refine ⟨m, ?_⟩
      rw [hgs, mul_div_assoc, div_self (hb l), mul_one]
      exact hm
    choose M hM using hbd
    set K := Finset.univ.sup M with hK
    have hy : f l ^ K / b l ∈ 1 / L := by
      rw [Submodule.mem_div_iff_forall_mul_mem]
      intro e he
      rw [hLG] at he
      induction he using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨s, rfl⟩ := hz
        rw [Submodule.mem_one]
        refine ⟨⟨f l ^ (K - M s) * (f l ^ M s * (g s / b l)), mul_mem (pow_mem (hf l) _) (hM s)⟩, ?_⟩
        change f l ^ (K - M s) * (f l ^ M s * (g s / b l)) = f l ^ K / b l * g s
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ s))]
        ring
      | zero => rw [mul_zero]; exact zero_mem _
      | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
      | smul a u _ hu =>
        have : f l ^ K / b l * (a • u) = a • (f l ^ K / b l * u) := by
          rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul]
          ring
        rw [this]
        exact Submodule.smul_mem _ a hu
    refine ⟨n l + K, ?_⟩
    have : f l ^ (n l + K) * 1 = g l * (f l ^ K / b l) := by
      rw [hg, mul_one, pow_add]
      field_simp [hb l]
    rw [this]
    exact Submodule.mul_mem_mul (hn l) hy
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
