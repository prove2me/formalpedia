-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.QRG.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:47:28.526051+00:00
-- url     : https://prove2.me/submissions/6012d729-00cf-47b8-b17b-44d9dd0d7aee

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_neg_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_sub_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_neg_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_sub_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_zero_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_sum_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_eq_zero_of_H
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_move
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_gm_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_gm
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_gm_Rel
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_Rel_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_card_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
namespace PI.UnitaryGroupMassFormula.AdIndexEq.QRG
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (hdet : J.det ≠ 0) (h2 : (2 : K) ≠ 0)
    (d : ℕ) : ∀ (k : ℕ) (e : Fin k → Fin n → K), n - k = d → (∀ i, H σ J (e i) (e i) ≠ 0) →
      (∀ i j, i ≠ j → H σ J (e i) (e j) = 0) →
      ∀ g : UJ σ J, (∀ i, gm σ J g *ᵥ e i = e i) → g ∈ S σ J := by
  classical
  have hHsymm := H_symm σ J hσ hJ
  have horth_rev : ∀ x v, H σ J x v = 0 → H σ J v x = 0 := by
    intro x v h
    rw [hHsymm x v, h, map_zero]
  have hlin : ∀ {m : ℕ} (f : Fin m → Fin n → K), (∀ i, H σ J (f i) (f i) ≠ 0) →
      (∀ i j, i ≠ j → H σ J (f i) (f j) = 0) → LinearIndependent K f := by
    intro m f hf ho
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := congrArg (H σ J (f j)) hc
    rw [H_sum_right, H_zero_right] at h1
    simp_rw [H_smul_right] at h1
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [ho j i (Ne.symm hij), mul_zero]) (by simp)] at h1
    exact (mul_eq_zero.mp h1).resolve_right (hf j)
  have fixS : ∀ g : UJ σ J, gm σ J g = 1 → g ∈ S σ J := by
    intro g hg
    have h1 : g = 1 := Subtype.ext (Units.ext hg)
    rw [h1]
    exact (S σ J).one_mem
  have gm_eq_one : ∀ g : UJ σ J, (∀ v, gm σ J g *ᵥ v = v) → gm σ J g = 1 := by
    intro g hv
    ext i j
    have h1 := congrFun (hv (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at h1
    simpa [Matrix.one_apply, Pi.single_apply] using h1
  have proj : ∀ {k : ℕ} (e : Fin k → Fin n → K), (∀ i, H σ J (e i) (e i) ≠ 0) →
      (∀ i j, i ≠ j → H σ J (e i) (e j) = 0) →
      ∀ z, ∃ v, (∀ i, H σ J (e i) v = 0) ∧ z - v ∈ Submodule.span K (Set.range e) := by
    intro k e he ho z
    refine ⟨z - ∑ i, ((H σ J (e i) (e i))⁻¹ * H σ J (e i) z) • e i, ?_, ?_⟩
    · intro j
      rw [H_sub_right, H_sum_right]
      simp_rw [H_smul_right]
      rw [Finset.sum_eq_single j (fun i _ hij => by rw [ho j i (Ne.symm hij), mul_zero]) (by simp)]
      rw [mul_comm ((H σ J (e j) (e j))⁻¹), mul_assoc, inv_mul_cancel₀ (he j), mul_one, sub_self]
    · rw [sub_sub_cancel]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have aniso : ∀ {k : ℕ} (e : Fin k → Fin n → K), k < n → (∀ i, H σ J (e i) (e i) ≠ 0) →
      (∀ i j, i ≠ j → H σ J (e i) (e j) = 0) →
      ∃ w, (∀ i, H σ J (e i) w = 0) ∧ H σ J w w ≠ 0 := by
    intro k e hk he ho
    have hspan : Submodule.span K (Set.range e) ≠ ⊤ := by
      intro htop
      have h1 := finrank_range_le_card (R := K) e
      unfold Set.finrank at h1
      rw [htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
      omega
    obtain ⟨z, hz⟩ : ∃ z, z ∉ Submodule.span K (Set.range e) := by
      by_contra hall
      push_neg at hall
      exact hspan (eq_top_iff.mpr (fun z _ => hall z))
    obtain ⟨v, hvW, hzv⟩ := proj e he ho z
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [sub_zero] at hzv
      exact hz hzv
    obtain ⟨z2, hz2⟩ : ∃ z2, H σ J v z2 ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hv0 (eq_zero_of_H σ J hdet v hall)
    obtain ⟨v2, hv2W, hzv2⟩ := proj e he ho z2
    have hvspan : ∀ x ∈ Submodule.span K (Set.range e), H σ J v x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact horth_rev _ _ (hvW i)
      | zero => exact H_zero_right σ J v
      | add x y _ _ hx hy => rw [H_add_right, hx, hy, add_zero]
      | smul c x _ hx => rw [H_smul_right, hx, mul_zero]
    have hvv2 : H σ J v v2 ≠ 0 := by
      intro h0
      apply hz2
      have e1 : z2 = v2 + (z2 - v2) := by abel
      rw [e1, H_add_right, h0, hvspan _ hzv2, add_zero]
    by_cases h1 : H σ J v v = 0
    · by_cases h2' : H σ J v2 v2 = 0
      · refine ⟨v + σ (H σ J v v2) • v2, ?_, ?_⟩
        · intro i
          rw [H_add_right, H_smul_right, hvW i, hv2W i, mul_zero, add_zero]
        · have hsb : σ (H σ J v v2) ≠ 0 := (map_ne_zero σ).mpr hvv2
          intro h0
          rw [H_add_left, H_add_right, H_add_right, H_smul_left, H_smul_right, H_smul_right,
            H_smul_left, h1, h2', hσ, hHsymm v v2] at h0
          exact mul_ne_zero h2 (mul_ne_zero hvv2 hsb) (by linear_combination h0)
      · exact ⟨v2, hv2W, h2'⟩
    · exact ⟨v, hvW, h1⟩
  induction d with
  | zero =>
    intro k e hnk he ho g hg
    have hkn : k ≤ n := card_le σ J e he ho
    have hk : k = n := by omega
    apply fixS
    apply gm_eq_one
    have hli := hlin e he ho
    have h3 : Module.finrank K (Submodule.span K (Set.range e)) = n := by
      have h4 := linearIndependent_iff_card_eq_finrank_span.mp hli
      unfold Set.finrank at h4
      rw [Fintype.card_fin] at h4
      exact h4.symm.trans hk
    have hspan : Submodule.span K (Set.range e) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h3, Module.finrank_fin_fun])
    intro v
    have hv : v ∈ Submodule.span K (Set.range e) := by rw [hspan]; exact Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hg i
    | zero => exact Matrix.mulVec_zero _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx]
  | succ d ih =>
    intro k e hnk he ho g hg
    obtain ⟨w, hwe, hww⟩ := aniso e (by omega) he ho
    have he'a : ∀ i, H σ J ((Fin.snoc e w : Fin (k + 1) → Fin n → K) i)
        ((Fin.snoc e w : Fin (k + 1) → Fin n → K) i) ≠ 0 := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hww
      · simpa using he j
    have he'o : ∀ i j, i ≠ j → H σ J ((Fin.snoc e w : Fin (k + 1) → Fin n → K) i)
        ((Fin.snoc e w : Fin (k + 1) → Fin n → K) j) = 0 := by
      intro i j
      refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro hij
        exact absurd rfl hij
      · intro _
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact horth_rev _ _ (hwe j')
      · intro _
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact hwe i'
      · intro hij
        simp only [Fin.snoc_castSucc]
        exact ho i' j' (fun h => hij (by rw [h]))
    have hnk' : n - (k + 1) = d := by omega
    have key : ∀ g' : UJ σ J, (∀ i, gm σ J g' *ᵥ e i = e i) → gm σ J g' *ᵥ w = w → g' ∈ S σ J := by
      intro g' hg'e hg'w
      apply ih (k + 1) (Fin.snoc e w) hnk' he'a he'o g'
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hg'w
      · simpa using hg'e j
    have huu : H σ J (gm σ J g *ᵥ w) (gm σ J g *ᵥ w) = H σ J w w := H_gm σ J g w w
    have hue : ∀ i, H σ J (gm σ J g *ᵥ w) (e i) = 0 := by
      intro i
      calc H σ J (gm σ J g *ᵥ w) (e i) = H σ J (gm σ J g *ᵥ w) (gm σ J g *ᵥ e i) := by rw [hg i]
        _ = H σ J w (e i) := H_gm σ J g w (e i)
        _ = 0 := horth_rev _ _ (hwe i)
    by_cases hA : H σ J (gm σ J g *ᵥ w - w) (gm σ J g *ᵥ w - w) = 0
    · have hpw : H σ J (gm σ J g *ᵥ w - -w) (gm σ J g *ᵥ w - -w) ≠ 0 := by
        rw [sub_neg_eq_add]
        intro h0
        apply mul_ne_zero (mul_ne_zero h2 h2) hww
        have e1 : H σ J (gm σ J g *ᵥ w + w) (gm σ J g *ᵥ w + w) +
            H σ J (gm σ J g *ᵥ w - w) (gm σ J g *ᵥ w - w) =
            2 * H σ J (gm σ J g *ᵥ w) (gm σ J g *ᵥ w) + 2 * H σ J w w := by
          rw [H_add_left, H_add_right, H_add_right, H_sub_left, H_sub_right, H_sub_right]
          ring
        rw [huu, h0, hA] at e1
        linear_combination -e1
      obtain ⟨α, hα, hαu, hαfix⟩ := move σ J hσ hJ (gm σ J g *ᵥ w) (-w)
        (by rw [H_neg_left, H_neg_right, neg_neg, huu]) hpw
      have hR1 := Rel_mem σ J hσ hJ _ α hα hpw
      have hm1 : σ (-1) * (-1 : K) = 1 := by simp
      have hR2 := Rel_mem σ J hσ hJ w (-1) hm1 hww
      have hR2w : Rm σ J w (-1) *ᵥ (-w) = w := by
        rw [Rm_mulVec, H_neg_right, mul_neg, inv_mul_cancel₀ hww,
          show ((-1 : K) - 1) * -1 = 2 by ring, two_smul]
        abel
      have hR2e : ∀ i, Rm σ J w (-1) *ᵥ e i = e i := by
        intro i
        rw [Rm_mulVec, horth_rev _ _ (hwe i), mul_zero, mul_zero, zero_smul, add_zero]
      have hR1e : ∀ i, Rm σ J (gm σ J g *ᵥ w - -w) α *ᵥ e i = e i := fun i =>
        hαfix (e i) (by rw [H_sub_left, H_neg_left, hue i, horth_rev _ _ (hwe i), neg_zero, sub_zero])
      have hTS : (Rel σ J hσ hJ w (-1) hm1 hww * Rel σ J hσ hJ _ α hα hpw) * g ∈ S σ J := by
        apply key
        · intro i
          rw [gm_mul, gm_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg i, gm_Rel, gm_Rel,
            hR1e, hR2e]
        · rw [gm_mul, gm_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gm_Rel, gm_Rel, hαu, hR2w]
      have e2 : g = (Rel σ J hσ hJ w (-1) hm1 hww * Rel σ J hσ hJ _ α hα hpw)⁻¹ *
          ((Rel σ J hσ hJ w (-1) hm1 hww * Rel σ J hσ hJ _ α hα hpw) * g) := by group
      rw [e2]
      exact (S σ J).mul_mem ((S σ J).inv_mem ((S σ J).mul_mem hR2 hR1)) hTS
    · obtain ⟨α, hα, hαu, hαfix⟩ := move σ J hσ hJ (gm σ J g *ᵥ w) w huu hA
      have hR := Rel_mem σ J hσ hJ _ α hα hA
      have hR1e : ∀ i, Rm σ J (gm σ J g *ᵥ w - w) α *ᵥ e i = e i := fun i =>
        hαfix (e i) (by rw [H_sub_left, hue i, horth_rev _ _ (hwe i), sub_zero])
      have hTS : Rel σ J hσ hJ _ α hα hA * g ∈ S σ J := by
        apply key
        · intro i
          rw [gm_mul, ← Matrix.mulVec_mulVec, hg i, gm_Rel, hR1e]
        · rw [gm_mul, ← Matrix.mulVec_mulVec, gm_Rel, hαu]
      have e2 : g = (Rel σ J hσ hJ _ α hα hA)⁻¹ * (Rel σ J hσ hJ _ α hα hA * g) := by group
      rw [e2]
      exact (S σ J).mul_mem ((S σ J).inv_mem hR) hTS
end PI.UnitaryGroupMassFormula.AdIndexEq.QRG
