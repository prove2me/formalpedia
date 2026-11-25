-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleRing_twist_subset_4861de94ddb8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:42.758003+00:00
-- url     : https://prove2.me/submissions/b1dd1123-a655-4ff3-96a7-a47c27ad528d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_twist_pow_sub_866f2c84b38e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_mem_ampleRing_b9b40574ef39


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
open scoped Pointwise
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
theorem _root_.solution (G H : SubSystem S x Ω) {r₁ r₂ : ℕ} (g : Fin (r₁ + 1) → Ω)
    (h : Fin (r₂ + 1) → Ω)
    (hgI : ∀ I, Submodule.span (chartRing S x I) (Set.range g) = G.sub I) (hh : IsVeryAmpleBy H h)
    {b₀ : Fin (r₁ + 1)} {l₀ : Fin (r₂ + 1)} (hne : h l₀ * g b₀ ≠ 0) (T : Subalgebra S Ω)
    (hT : ∀ b m, h m * g b / (h l₀ * g b₀) ∈ T) :
    ampleRing (G.twist H) 1 (h l₀ * g b₀) ⊆ T := by
  classical
  set p := h l₀ * g b₀ with hp
  have hl₀ : h l₀ ≠ 0 := left_ne_zero_of_mul hne
  have hb₀ : g b₀ ≠ 0 := right_ne_zero_of_mul hne
  have hB : ampleRing H 1 (h l₀) ⊆ T := by
    intro y hy
    have hy' := hh.closed l₀ hl₀ hy
    refine (Algebra.adjoin_le ?_ : ampleBase (S := S) h l₀ ≤ T) hy'
    rintro _ ⟨m, rfl⟩
    have : h m / h l₀ = h m * g b₀ / p := by rw [hp, mul_div_mul_right _ _ hb₀]
    show h m / h l₀ ∈ T
    rw [this]; exact hT b₀ m
  have hPn : ∀ n : ℕ, ∀ t ∈ (Set.range h * Set.range g) ^ n, t / p ^ n ∈ T := by
    intro n
    induction n with
    | zero =>
      intro t ht
      rw [pow_zero, Set.mem_one] at ht
      rw [ht, pow_zero, div_one]; exact one_mem T
    | succ n ih =>
      intro t ht
      rw [pow_succ, Set.mem_mul] at ht
      obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht
      obtain ⟨_, ⟨m, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp ht₂
      have : t₁ * (h m * g b) / p ^ (n + 1) = (t₁ / p ^ n) * (h m * g b / p) := by
        rw [pow_succ, mul_div_mul_comm]
      rw [this]
      exact mul_mem (ih t₁ ht₁) (hT b m)
  obtain ⟨n, a, b, J, ha, hb, hsum, hJ⟩ := hh.affine l₀ hl₀
  intro y hy
  have hloc : ∀ k, ∃ e : ℕ, b k ^ e * y ∈ T := by
    intro k
    obtain ⟨n', hn'⟩ := Set.mem_iInter.mp hy (J k)
    rw [one_mul, twist_pow_sub, ← hgI (J k), ← hh.generates (J k), Submodule.span_mul_span,
      Submodule.span_pow] at hn'
    have hbT : b k ∈ T := hB (hb k)
    suffices hQ : ∀ z ∈ Submodule.span (chartRing S x (J k)) ((Set.range h * Set.range g) ^ n'),
        ∃ e : ℕ, b k ^ e * (z / p ^ n') ∈ T by
      obtain ⟨e, he⟩ := hQ _ hn'
      rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hne)] at he
      exact ⟨e, he⟩
    intro z hz
    induction hz using Submodule.span_induction with
    | mem t ht => exact ⟨0, by rw [pow_zero, one_mul]; exact hPn n' t ht⟩
    | zero => exact ⟨0, by rw [zero_div, mul_zero]; exact zero_mem T⟩
    | add z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨e₁, he₁⟩ := h₁
      obtain ⟨e₂, he₂⟩ := h₂
      refine ⟨e₁ + e₂, ?_⟩
      have : b k ^ (e₁ + e₂) * ((z₁ + z₂) / p ^ n') =
          b k ^ e₂ * (b k ^ e₁ * (z₁ / p ^ n')) + b k ^ e₁ * (b k ^ e₂ * (z₂ / p ^ n')) := by
        rw [pow_add, add_div]; ring
      rw [this]
      exact add_mem (mul_mem (pow_mem hbT _) he₁) (mul_mem (pow_mem hbT _) he₂)
    | smul c z _ hz =>
      obtain ⟨e₂, he₂⟩ := hz
      obtain ⟨e₁, he₁⟩ := exists_pow_mul_mem_ampleRing H (h l₀) (b k) (J k) (hb k) (hJ k) c.2
      refine ⟨e₁ + e₂, ?_⟩
      have : b k ^ (e₁ + e₂) * (c • z / p ^ n') = (b k ^ e₁ * c) * (b k ^ e₂ * (z / p ^ n')) := by
        rw [chartRing_smul_def, pow_add]; ring
      rw [this]
      exact mul_mem (hB he₁) he₂
  choose e he using hloc
  let bT : Fin n → T := fun k => ⟨b k, hB (hb k)⟩
  have htop : Ideal.span (Set.range bT) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : T) = ∑ k, (⟨a k, hB (ha k)⟩ : T) * bT k := by
      apply Subtype.ext
      simp only [bT]
      push_cast
      exact hsum.symm
    rw [h1]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
  set E := ∑ k, e k
  have h1 : (1 : T) ∈ Ideal.span ((fun z : T => z ^ E) '' Set.range bT) := by
    rw [Ideal.span_pow_eq_top _ htop E]; trivial
  suffices hP : ∀ t ∈ Ideal.span ((fun z : T => z ^ E) '' Set.range bT), (t : Ω) * y ∈ T by
    simpa using hP 1 h1
  intro t ht
  induction ht using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hz
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (fun k _ => Nat.zero_le (e k)) (Finset.mem_univ k))
    have : ((bT k ^ E : T) : Ω) * y = b k ^ d * (b k ^ e k * y) := by
      simp only [SubmonoidClass.coe_pow, bT]
      rw [show E = e k + d from hd, pow_add]; ring
    rw [this]
    exact mul_mem (pow_mem (hB (hb k)) _) (he k)
  | zero => simp
  | add t₁ t₂ _ _ h₁ h₂ =>
    rw [Subalgebra.coe_add, add_mul]; exact add_mem h₁ h₂
  | smul c t _ ht =>
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_assoc]; exact mul_mem c.2 ht
end GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
