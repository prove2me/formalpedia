-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.SU_eq_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:51:48.660871+00:00
-- url     : https://prove2.me/submissions/cfea9e74-118a-4b60-9b47-7c75db065565

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_HfDecompSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SubProjOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SUEqClosure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_move
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_fix_all_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_SU_preserves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eichAlong_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_exists_spans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_SU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_of_closure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_preserves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_gp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_mul_mem_SU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_one_mem_SU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x) {i2 : K} (h2i : 2 * i2 = 1) {δ : K} (hδ : IsUnit δ)
  (hσδ : σ δ = -δ) [IsReduced K]
  (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal → m₂.IsMaximal →
      m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂)
include hσ hJ he hff hef hfix h2i hδ hσδ
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (hdet : IsUnit J.det) [Nontrivial K]
    (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal → m₂.IsMaximal →
      m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂) :
    SU σ J = (Submonoid.closure (eichSet σ J e f) : Set (Matrix ι ι K)) := by
  ext g
  constructor
  · intro hg
    have hdetg : g.det = 1 := hg.1
    have hpresg : ∀ x y, hf σ J (g *ᵥ x) (g *ᵥ y) = hf σ J x y := by
      intro x y; apply SU_preserves (hg := hg) <;> first | exact hδ | exact hσδ | assumption
    obtain ⟨r, F, hF⟩ : ∃ r, ∃ F : OFam σ J e f r, F.Spans := by
      apply exists_spans hσ hJ he hff hef hdet hfix
      all_goals first
        | exact hσδ | exact hδ | assumption
        | exact (Units.mkOfMulEqOne _ _ h2i).isUnit
    have gp : ∀ p ∈ Good σ J e f, ∀ x y, hf σ J (p *ᵥ x) (p *ᵥ y) = hf σ J x y := by
      intro p hp x y; exact good_preserves hσ hJ he hff hef F.ha_e F.ha_f hp x y
    have hunit : ∀ k, IsUnit (hf σ J (F.a k) (F.a k)) := fun k =>
      (Units.mkOfMulEqOne _ (F.inv k) (by rw [mul_comm]; exact F.hinv k)).isUnit
    have step : ∀ k, k ≤ r → ∃ p ∈ Good σ J e f, ∀ j : Fin r, j.val < k →
        (p * g) *ᵥ F.a j = F.a j := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨1, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
        apply good_of_closure (hn := Submonoid.one_mem _) <;> first | exact hδ | exact hσδ | assumption
      | succ k ih =>
        intro hk
        obtain ⟨p, hp, hpa⟩ := ih (by omega)
        set a' : Fin k → ι → K := fun j => F.a ⟨j.val, by omega⟩ with ha'
        have hae' : ∀ j, hf σ J (a' j) e = 0 := fun j => F.ha_e _
        have haf' : ∀ j, hf σ J (a' j) f = 0 := fun j => F.ha_f _
        set kk : Fin r := ⟨k, by omega⟩ with hkk
        set b := (p * g) *ᵥ F.a kk with hbdef
        have hpg : ∀ x y, hf σ J ((p * g) *ᵥ x) ((p * g) *ᵥ y) = hf σ J x y := by
          intro x y; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gp p hp, hpresg]
        have hne : ∀ j : Fin k, (⟨j.val, by omega⟩ : Fin r) ≠ kk := by
          intro j h
          have h1 := congrArg Fin.val h
          have h2 := j.isLt
          simp only [hkk, Fin.val_mk] at h1
          omega
        have hbk : ∀ j, hf σ J b (a' j) = 0 := by
          intro j
          show hf σ J b (F.a ⟨j.val, by omega⟩) = 0
          rw [← hpa ⟨j.val, by omega⟩ j.isLt, hbdef, hpg]
          exact F.ho _ _ (Ne.symm (hne j))
        have hak : ∀ j, hf σ J (F.a kk) (a' j) = 0 := fun j => F.ho _ _ (Ne.symm (hne j))
        have hbb : hf σ J b b = hf σ J (F.a kk) (F.a kk) := by rw [hbdef, hpg]
        have m1 : Reach σ J e f a' b (e + (hf σ J b b * i2) • f) := by
          apply move (hae := hae') (haf := haf') (hmax := hmax) (hb := hbk)
            (hν := by rw [hbb]; exact hunit kk) <;> first | exact hδ | exact hσδ | assumption
        have m2 : Reach σ J e f a' (F.a kk) (e + (hf σ J (F.a kk) (F.a kk) * i2) • f) := by
          apply move (hae := hae') (haf := haf') (hmax := hmax) (hb := hak) (hν := hunit kk) <;>
            first | exact hδ | exact hσδ | assumption
        rw [hbb] at m1
        have m3 : Reach σ J e f a' (e + (hf σ J (F.a kk) (F.a kk) * i2) • f) (F.a kk) := by
          apply reach_symm (h := m2) <;> first | exact hδ | exact hσδ | assumption
        have m4 : Reach σ J e f a' b (F.a kk) := by
          apply reach_trans (h1 := m1) (h2 := m3) <;> first | exact hδ | exact hσδ | assumption
        obtain ⟨q, hq, hqa, hqb⟩ := m4
        refine ⟨q * p, ?_, fun j hj => ?_⟩
        · apply good_mul (hg := hq) (hg' := hp) <;> first | exact hδ | exact hσδ | assumption
        · rw [mul_assoc, ← Matrix.mulVec_mulVec]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
          · rw [hpa j hj']
            have := hqa ⟨j.val, hj'⟩
            simpa [ha'] using this
          · have hjk : j = kk := Fin.ext (by simp [hkk, hj'])
            rw [hjk, ← hbdef, hqb]
    obtain ⟨p, hp, hpa⟩ := step r le_rfl
    have hpgood : p * g ∈ Good σ J e f := by
      apply fix_all_good (F := F) (hF := hF) (hpres := fun x y => by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gp p hp, hpresg])
        (hfixa := fun j => hpa j j.isLt) <;> first | exact hδ | exact hσδ | assumption
    obtain ⟨p', hp', hp'p, -⟩ : ∃ g' ∈ Good σ J e f, g' * p = 1 ∧ p * g' = 1 := by
      apply good_inv (hg := hp) <;> first | exact hδ | exact hσδ | assumption
    have hgg : g ∈ Good σ J e f := by
      have : g = p' * (p * g) := by rw [← mul_assoc, hp'p, one_mul]
      rw [this]
      apply good_mul (hg := hp') (hg' := hpgood) <;> first | exact hδ | exact hσδ | assumption
    apply good_SU (hδ := hδ) (hσδ := hσδ) (hg := hgg) (hdet := hdetg) <;> first | exact hδ | exact hσδ | assumption
  · intro hg
    rw [SetLike.mem_coe] at hg
    induction hg using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact (by apply eichAlong_sub (he := he) <;> first | exact hδ | exact hσδ | assumption : eichAlong σ J e f ⊆ SU σ J) hx
      · exact (by apply eichAlong_sub (he := hff) <;> first | exact hδ | exact hσδ | assumption : eichAlong σ J f e ⊆ SU σ J) hx
    | one => apply one_mem_SU <;> first | exact hδ | exact hσδ | assumption
    | mul x y _ _ hx hy => apply mul_mem_SU (hg := hx) (hh := hy) <;> first | exact hδ | exact hσδ | assumption
end ReciprocityTheory.ChartRestriction.G.SA
