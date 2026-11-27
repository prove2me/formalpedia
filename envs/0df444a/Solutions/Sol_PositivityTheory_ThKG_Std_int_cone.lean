-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.int_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:23:03.157641+00:00
-- url     : https://prove2.me/submissions/48e3874a-f267-479c-848e-ceb613cd11ee

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_SplitProd
import Theorems.Thm_PositivityTheory_ThKG_Std_detB
import Theorems.Thm_PositivityTheory_ThKG_Std_detA
import Theorems.Thm_PositivityTheory_ThKG_Std_ext_mid
import Theorems.Thm_PositivityTheory_ThKG_Std_ext_off
import Theorems.Thm_PositivityTheory_ThKG_Std_rad_le
import Theorems.Thm_PositivityTheory_ThKG_Std_rad_e
import Theorems.Thm_PositivityTheory_ThKG_Std_ind_zero
import Theorems.Thm_PositivityTheory_ThKG_Std_val_det
import Theorems.Thm_PositivityTheory_ThKG_Std_prod_mid
import Theorems.Thm_PositivityTheory_ThKG_Std_prod_vol
import Theorems.Thm_PositivityTheory_ThKG_Std_split_prod
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_mul
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_of_ne
import Theorems.Thm_PositivityTheory_ThKG_Std_gI_neg
import Theorems.Thm_PositivityTheory_ThKG_Std_ind_ne
import Theorems.Thm_PositivityTheory_ThKG_Std_int_ind_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n d n₁ d₁ : ℕ} {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
variable {jr : Fin n₁ → Fin n} {jc : Fin d₁ → Fin d}
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}
namespace PositivityTheory.ThKG.Std
theorem _root_.solution (hm : IsVol m) (hϖ : IsUnif ϖ) {b : ℕ} {jc : Fin d₁ → Fin d} (hc : Function.Injective jc) {e : Fin (b + 2) → Fin d}
    {e₁ : Fin b → Fin d₁} (hei : Function.Injective e) (he : ∀ i, jc (e₁ i) = e (mid i))
    (h0 : ∀ j, e 0 ≠ jc j) (h1 : ∀ j, e (Fin.last _) ≠ jc j) (P : Finset (Fin (b + 2) × Fin d)) (hP : ∀ i j, (mid i, jc j) ∉ P)
    (ha : (Fin.last _, e 0) ∈ P) (hb : (0, e (Fin.last _)) ∉ P)
    (hAB : ((∀ j, j ≠ Fin.last _ → (0, e j) ∉ P) ∧ ∀ i, (mid i, e 0) ∉ P) ∨
      ((∀ i, i ≠ 0 → (i, e (Fin.last _)) ∉ P) ∧ ∀ j, (Fin.last _, e (mid j)) ∉ P)) {r : ℕ}
    (g : Fin r → Fin (b + 2) × Fin d) (hg : Function.Injective g) (h : ∀ p, p ∈ Set.range g ↔ p ∈ P ∧ p.2 ∉ Set.range e)
    (y : Matrix (Fin b) (Fin d₁) k) (s t : k) :
    ∫ Z, ψ (-(t * Z (Fin.last _, e 0))) * std ν ϖ c e (tm (cut P Z) + (ext mid jc y + single 0 (e (Fin.last _)) s)) * wt P Z
      ∂(Measure.pi fun _ => m) = (((resCard k : ℂ) ^ c)⁻¹) ^ r * (dl ν s * gI m ψ ν t) * std ν ϖ c e₁ y := by
  haveI := hm.haar
  have hmi : Function.Injective (mid : Fin b → _) := fun _ _ h => Fin.ext (by simpa [mid] using congrArg Fin.val h)
  have m0 : ∀ i : Fin b, (0 : Fin (b + 2)) ≠ mid i := fun i h => by simpa [mid] using congrArg Fin.val h
  have ml : ∀ i : Fin b, Fin.last (b + 1) ≠ mid i := fun i h => by
    have := congrArg Fin.val h; simp [mid] at this; omega
  have l0 : Fin.last (b + 1) ≠ 0 := by simp
  set Y := ext mid jc y + single 0 (e (Fin.last _)) s with hYd
  have hE : ∀ p ∈ P, ext mid jc y p.1 p.2 = 0 := fun p hp => ext_off y (by
    by_contra h
    push Not at h
    obtain ⟨⟨i, hi⟩, j, hj⟩ := h
    exact hP i j (by rw [← hi, ← hj]; exact hp))
  have hY : ∀ p ∈ P, Y p.1 p.2 = 0 := fun p hp => by
    rw [hYd, Matrix.add_apply, hE p hp, single_apply_of_ne, add_zero]
    rintro ⟨a, b⟩
    exact hb (by rw [a, b]; exact hp)
  have hd : ∀ Z, ((tm (cut P Z) + Y).submatrix id e).det = s * -Z (Fin.last _, e 0) * (y.submatrix id e₁).det := fun Z => by
    have e1 : ((tm (cut P Z) + Y).submatrix id e).submatrix mid mid = y.submatrix id e₁ := by
      ext i j
      have := hP i (e₁ j)
      simp [tm, cut, hYd, ← he, this, ext_mid hmi hc, single_apply, m0]
    have e2 : (tm (cut P Z) + Y).submatrix id e 0 (Fin.last _) = s := by
      simp [tm, cut, hYd, hb, ext_off y (Or.inl m0)]
    have e3 : (tm (cut P Z) + Y).submatrix id e (Fin.last _) 0 = Z (Fin.last _, e 0) := by
      have := hY _ ha
      simp only [submatrix_apply, id, Matrix.add_apply, this, tm, of_apply, cut, if_pos ha, add_zero]
    rcases hAB with ⟨x1, x2⟩ | ⟨x1, x2⟩
    · rw [detB _ (fun j hj => by simp [tm, cut, hYd, x1 j hj, ext_off y (Or.inl m0), single_apply, hei.eq_iff, hj.symm])
        (fun i => by simp [tm, cut, hYd, x2 i, ext_off y (Or.inr h0), single_apply, m0]), e1, e2, e3]
      ring
    · rw [detA _ (fun i hi => by simp [tm, cut, hYd, x1 i hi, ext_off y (Or.inr h1), single_apply, hi.symm])
        (fun j => by simp [tm, cut, hYd, x2 j, ext_off y (Or.inl ml), single_apply, l0.symm]), e1, e2, e3]
      ring
  have hr : ∀ j, jc j ∈ Set.range e ↔ j ∈ Set.range e₁ := fun j => by
    refine ⟨fun ⟨i, hi⟩ => ?_, fun ⟨i, hi⟩ => ⟨mid i, by rw [← he, hi]⟩⟩
    have a0 : i ≠ 0 := fun h => h0 j (h ▸ hi)
    have a1 : i ≠ Fin.last _ := fun h => h1 j (h ▸ hi)
    have a0' : i.1 ≠ 0 := fun h => a0 (Fin.ext h)
    have a1' : i.1 ≠ b + 1 := fun h => a1 (Fin.ext h)
    have : i = mid ⟨i.1 - 1, by omega⟩ := Fin.ext (by simp [mid]; omega)
    exact ⟨_, hc ((he _).trans (this ▸ hi))⟩
  have hA : (∏ p : Fin (b + 2) × Fin d, if p ∈ P then 1 else ind (rad ϖ c e p.2) (Y p.1 p.2)) =
      (∏ p : Fin b × Fin d₁, ind (rad ϖ c e₁ p.2) (y p.1 p.2)) * ind 1 s := by
    rw [← prod_mid hmi hc hr hP y, ← Finset.prod_ite_eq_of_mem' Finset.univ ((0 : Fin (b + 2)), e (Fin.last _)) (fun _ => ind 1 s)
      (Finset.mem_univ _), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    by_cases hp : p = (0, e (Fin.last _))
    · subst hp
      simp [hb, hYd, ext_off y (Or.inl m0), rad_e, ind_zero]
    · rw [if_neg hp, mul_one, hYd, Matrix.add_apply, single_apply_of_ne, add_zero]
      rintro ⟨a, b⟩
      exact hp (Prod.ext a.symm b.symm)
  let f : Fin (b + 2) × Fin d → k → ℂ := fun p x => (if p ∈ P then ind (rad ϖ c e p.2) x else ind 1 x) *
    if p = (Fin.last _, e 0) then dl ν (-x) * ψ (-(t * x)) else 1
  have key : ∀ Z, ψ (-(t * Z (Fin.last _, e 0))) * std ν ϖ c e (tm (cut P Z) + Y) * wt P Z =
      dl ν s * std ν ϖ c e₁ y * ∏ p, f p (Z p) := fun Z => by
    have e1 := split_prod (ϖ := ϖ) (c := c) (e := e) P Y hY Z
    rw [hA] at e1
    simp only [f, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true, std, hd]
    set A := ∏ p : Fin b × Fin d₁, ind (rad ϖ c e₁ p.2) (y p.1 p.2) with hA'
    set Q := ∏ p : Fin (b + 2) × Fin d, (if p ∈ P then ind (rad ϖ c e p.2) (Z p) else ind 1 (Z p)) with hQ
    have e2 : A * ind 1 s * Q * dl ν (s * -Z (Fin.last _, e 0) * (y.submatrix id e₁).det) =
        A * Q * (dl ν s * dl ν (-Z (Fin.last _, e 0)) * dl ν (y.submatrix id e₁).det) := by
      by_cases a1 : A = 0
      · simp [a1]
      by_cases a2 : Q = 0
      · simp [a2]
      have b1 : valuation k (y.submatrix id e₁).det ≤ 1 := val_det fun i j =>
        (ind_ne (Finset.prod_ne_zero_iff.1 a1 (i, e₁ j) (Finset.mem_univ _))).trans (rad_le hϖ _ _)
      have b2 := Finset.prod_ne_zero_iff.1 a2 _ (Finset.mem_univ (Fin.last _, e 0))
      rw [if_pos ha] at b2
      have b3 : valuation k (-Z (Fin.last _, e 0)) ≤ 1 := by simpa using (ind_ne b2).trans (rad_le hϖ _ _)
      by_cases a3 : valuation k s ≤ 1
      · rw [dl_mul (by rw [map_mul]; exact mul_le_one' a3 b3) b1, dl_mul a3 b3, ind, if_pos (by simpa using a3), mul_one]
      · rw [ind, if_neg (by simpa using a3), dl_of_ne (x := s) fun h => a3 h.le]; simp
    linear_combination ψ (-(t * Z (Fin.last _, e 0))) * dl ν (s * -Z (Fin.last _, e 0) * (y.submatrix id e₁).det) * e1 +
      ψ (-(t * Z (Fin.last _, e 0))) * e2
  simp only [key]
  rw [integral_const_mul, integral_fintype_prod_eq_prod f, ← prod_vol hm hϖ g hg h,
    ← Finset.prod_ite_eq_of_mem' Finset.univ (Fin.last (b + 1), e 0) (fun _ => gI m ψ ν t) (Finset.mem_univ _)]
  have : ∏ p, ∫ x, f p x ∂m = (∏ p : Fin (b + 2) × Fin d, ∫ x, (if p ∈ P then ind (rad ϖ c e p.2) x else ind 1 x) ∂m) *
      ∏ p, if p = (Fin.last (b + 1), e 0) then gI m ψ ν t else 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    by_cases hp : p = (Fin.last (b + 1), e 0)
    · subst hp
      simp only [f, if_pos ha, if_true, rad_e, int_ind_one hm, one_mul, ← gI_neg hm]
      congr 1
      funext x
      by_cases hx : valuation k x ≤ 1
      · simp [ind, hx]
      · rw [dl_of_ne (x := -x) fun h => hx (by simpa using h.le)]; simp
    · simp only [f, if_neg hp, mul_one]
  rw [this]; ring
end PositivityTheory.ThKG.Std
