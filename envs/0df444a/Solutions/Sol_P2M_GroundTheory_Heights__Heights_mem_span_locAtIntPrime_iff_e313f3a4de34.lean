-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_span_locAtIntPrime_iff_e313f3a4de34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:11:38.919286+00:00
-- url     : https://prove2.me/submissions/ac680613-d0b3-4a81-b012-945657d4b481

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_eq_div_of_mem_locAtIntPrime_2a4c0a166d77

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution [CharZero Ω] {p : ℕ} (hp : p.Prime) (A : Subalgebra ℤ Ω)
    {E : Type} [AddCommGroup E] [Module Ω E] (L' : AddSubgroup E)
    (hL' : ∀ a ∈ A, ∀ e ∈ L', a • e ∈ L') (e : E) :
    e ∈ Submodule.span (locAtIntPrime p A.toSubring) (L' : Set E) ↔
      ∃ s : ℕ, ¬ p ∣ s ∧ (s : Ω) • e ∈ L' := by
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem x hx => exact ⟨1, hp.not_dvd_one, by simpa using hx⟩
    | zero => exact ⟨1, hp.not_dvd_one, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, fun h => (hp.dvd_mul.1 h).elim hs ht, ?_⟩
      rw [smul_add, Nat.cast_mul, mul_comm, mul_smul, mul_comm, mul_smul]
      exact add_mem (by simpa using hL' _ (A.natCast_mem t) _ hsx)
        (by simpa using hL' _ (A.natCast_mem s) _ hty)
    | smul u x _ hx =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨a, ha, t, ht, hu⟩ := exists_eq_div_of_mem_locAtIntPrime hp A u.2
      have h0 : (t : Ω) ≠ 0 := by
        rintro h; exact ht (by rw [show t = 0 by exact_mod_cast h]; exact dvd_zero p)
      refine ⟨t * s, fun h => (hp.dvd_mul.1 h).elim ht hs, ?_⟩
      rw [Subring.smul_def, hu, smul_smul, Nat.cast_mul,
        show (t : Ω) * s * (a * (t : Ω)⁻¹) = a * s by field_simp, ← smul_smul]
      exact hL' a ha _ hsx
  · rintro ⟨s, hs, hse⟩
    have h0 : (s : Ω) ≠ 0 := by
      rintro h; exact hs (by rw [show s = 0 by exact_mod_cast h]; exact dvd_zero p)
    have hinv : (s : Ω)⁻¹ ∈ locAtIntPrime p A.toSubring :=
      Subring.subset_closure (Or.inr ⟨s, fun h => hs (Int.natCast_dvd_natCast.1 h), by simp⟩)
    have : e = (⟨_, hinv⟩ : locAtIntPrime p A.toSubring) • ((s : Ω) • e) := by
      rw [Subring.smul_def, smul_smul, inv_mul_cancel₀ h0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hse)
end GroundTheory.Heights₂.Heights
