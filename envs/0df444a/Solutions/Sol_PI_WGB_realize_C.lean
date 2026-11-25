-- Prove2me | solution 1 for PI.WGB.realize_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:09.862074+00:00
-- url     : https://prove2.me/submissions/1588b3f7-a6c4-4346-869f-4c71957fb511

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_TransposeConjComm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_NatWAntiC
import Theorems.Thm_PI_WGB_natW_antiC
import Theorems.Thm_PI_WGB_twist_id
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwNe
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGB_embGL_coe
import Theorems.Thm_PI_WGB_fixed_data
import Theorems.Thm_PI_WGB_fockF_smul_left
import Theorems.Thm_PI_WGB_fockF_smul_right
import Theorems.Thm_PI_WGB_gram_of
import Theorems.Thm_PI_WGB_hwAt_shift
import Theorems.Thm_PI_WGB_iotaC_det
import Theorems.Thm_PI_WGB_iotaC_zero
import Theorems.Thm_PI_WGB_lc_zero_of_gram
import Theorems.Thm_PI_WGB_sqAct_eq
import Theorems.Thm_PI_WGB_sqAct_mulC
import Theorems.Thm_PI_WGB_sqAct_oneC
import Theorems.Thm_PI_WGB_sqLC_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
namespace PI.WGB
theorem _root_.solution (h : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) (n : ℕ) (lam : DomWeight (n + 1))
    (mu : DomWeight n) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) (hf : f ∈ nablaSq ℂ (n + 1) lam)
    (hfix : IsFixedW rfl lam mu f) (hne : f ≠ 0) :
    ∃ φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ,
      IsEqv rfl mu lam φ ∧ φ (extremal ℂ n mu) = f := by
  have hI : Interlace rfl lam mu := (ha n (n + 1) rfl lam mu f f hf hf hfix hfix hne).2
  have heM : extremal ℂ n mu ∈ nablaSq ℂ n mu := hwMem ℂ n n le_rfl mu.natW (natW_antiC mu)
  have heN : extremal ℂ n mu ≠ 0 := hwNe ℂ n n le_rfl mu.natW

  have hge : 0 < n → lam.detShift ≤ mu.detShift := by
    intro hn
    have h1 := (hI ⟨n - 1, by omega⟩).2
    have e1 : ∀ j : Fin (n + 1), j.val = n → lam.w j = lam.w ⟨n + 1 - 1, by omega⟩ :=
      fun j hj => congrArg lam.w (Fin.ext (by simp only; omega))
    rw [e1 _ (by simp only; omega)] at h1
    simp only [DomWeight.detShift, dif_pos hn, dif_pos (Nat.succ_pos n)]
    omega
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = (mu.detShift - lam.detShift).toNat := ⟨_, rfl⟩
  have hκ'e : ∀ i, (mu.natW i : ℤ) + mu.detShift = mu.w i := by
    intro i
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hle : mu.w ⟨n - 1, by omega⟩ ≤ mu.w i :=
      mu.anti (Fin.le_iff_val_le_val.mpr (by simp only; omega))
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hn] at hle ⊢
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hcE : 0 < n → mu.detShift = lam.detShift + (d : ℤ) := by
    intro hn
    have := hge hn
    rw [hd, Int.toNat_of_nonneg (by omega)]
    omega
  have hκf : ∀ i, ((mu.natW i + d : ℕ) : ℤ) + lam.detShift = mu.w i := by
    intro i
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have h1 := hκ'e i
    have h2 := hcE hn
    push_cast
    omega
  have hκfA : Antitone (fun i => mu.natW i + d) := fun i j hij => Nat.add_le_add_right (natW_antiC mu hij) d

  obtain ⟨hUf, hTf⟩ := fixed_data (k := 1) f lam.detShift mu.w (fun i => mu.natW i + d) hκf
    (fun g h1 h2 => by
      have := hfix.1 g h1 h2
      rwa [sqAct_eq, embGL_coe, iotaC_det] at this)
    (fun t => by
      have := hfix.2 t
      rw [sqAct_eq, embGL_coe, iotaC_det] at this
      have hdg : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
          Matrix.diagonal fun a => (t a : ℂ) := rfl
      rw [hdg, Matrix.det_diagonal, Units.coe_prod] at this
      simpa only [Units.val_zpow_eq_zpow_val] using this)
  obtain ⟨hUe, hTe⟩ := fixed_data (k := 0) (extremal ℂ n mu) mu.detShift mu.w mu.natW hκ'e
    (fun g h1 h2 => by
      rw [iotaC_zero]
      have := (he n mu).1 g h1 h2
      rwa [sqAct_eq] at this)
    (fun t => by
      rw [iotaC_zero]
      have := (he n mu).2.1 t
      rw [sqAct_eq] at this
      have hdg : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
          Matrix.diagonal fun a => (t a : ℂ) := rfl
      rw [hdg, Matrix.det_diagonal, Units.coe_prod] at this
      simpa only [Units.val_zpow_eq_zpow_val] using this)

  have gf : ∀ g g' : GL (Fin n) ℂ, fockF (vfC n lam f g) (vfC n lam f g') =
      ((g : Matrix (Fin n) (Fin n) ℂ).det ^ lam.detShift * star ((g' : Matrix (Fin n) (Fin n) ℂ).det ^ lam.detShift)) *
        (fockF f f * hwAt (fun i => mu.natW i + d)
          ((g' : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (g : Matrix (Fin n) (Fin n) ℂ))) := by
    intro g g'
    unfold vfC
    rw [sqAct_eq, sqAct_eq, embGL_coe, embGL_coe, iotaC_det, iotaC_det, fockF_smul_left, fockF_smul_right,
      gram_of _ hκfA hUf hTf]
    ring
  have ge : ∀ g g' : GL (Fin n) ℂ, fockF (veC n mu g) (veC n mu g') =
      ((g : Matrix (Fin n) (Fin n) ℂ).det ^ mu.detShift * star ((g' : Matrix (Fin n) (Fin n) ℂ).det ^ mu.detShift)) *
        (fockF (extremal ℂ n mu) (extremal ℂ n mu) * hwAt mu.natW
          ((g' : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (g : Matrix (Fin n) (Fin n) ℂ))) := by
    intro g g'
    unfold veC
    have := gram_of (k := 0) (f := extremal ℂ n mu) mu.natW (natW_antiC mu) hUe hTe
      (g : Matrix (Fin n) (Fin n) ℂ) (g' : Matrix (Fin n) (Fin n) ℂ)
    rw [iotaC_zero, iotaC_zero] at this
    rw [sqAct_eq, sqAct_eq, fockF_smul_left, fockF_smul_right, this]
    ring
  have hee : fockF (extremal ℂ n mu) (extremal ℂ n mu) ≠ 0 := by
    intro h0
    have := (fockPos _ (extremal ℂ n mu) heN).1
    rw [h0] at this
    simp at this
  have hK : ∀ g g' : GL (Fin n) ℂ, fockF (vfC n lam f g) (vfC n lam f g') =
      (fockF f f / fockF (extremal ℂ n mu) (extremal ℂ n mu)) * fockF (veC n mu g) (veC n mu g') := by
    intro g g'
    rw [gf, ge, hwAt_shift, Matrix.det_mul, Matrix.det_conjTranspose]
    have ha0 : (g : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    have hb0 : (g' : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    have tw : (g : Matrix (Fin n) (Fin n) ℂ).det ^ lam.detShift * star ((g' : Matrix (Fin n) (Fin n) ℂ).det ^ lam.detShift) *
        (star (g' : Matrix (Fin n) (Fin n) ℂ).det * (g : Matrix (Fin n) (Fin n) ℂ).det) ^ d =
        (g : Matrix (Fin n) (Fin n) ℂ).det ^ mu.detShift * star ((g' : Matrix (Fin n) (Fin n) ℂ).det ^ mu.detShift) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp [Matrix.det_isEmpty]
      · exact twist_id _ _ ha0 hb0 _ _ _ (hcE hn)
    set a := (g : Matrix (Fin n) (Fin n) ℂ).det
    set b := (g' : Matrix (Fin n) (Fin n) ℂ).det
    set H := hwAt mu.natW ((g' : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (g : Matrix (Fin n) (Fin n) ℂ))
    set ee := fockF (extremal ℂ n mu) (extremal ℂ n mu)
    calc a ^ lam.detShift * star (b ^ lam.detShift) * (fockF f f * ((star b * a) ^ d * H))
        = (a ^ lam.detShift * star (b ^ lam.detShift) * (star b * a) ^ d) * fockF f f * H := by ring
      _ = (a ^ mu.detShift * star (b ^ mu.detShift)) * fockF f f * H := by rw [tw]
      _ = (fockF f f / ee * ee) * (a ^ mu.detShift * star (b ^ mu.detShift)) * H := by
          rw [div_mul_cancel₀ _ hee]; ring
      _ = fockF f f / ee * (a ^ mu.detShift * star (b ^ mu.detShift) * (ee * H)) := by ring

  set Le := Finsupp.linearCombination ℂ (veC n mu) with hLe
  set Lf := Finsupp.linearCombination ℂ (vfC n lam f) with hLf
  have hker : LinearMap.ker Le ≤ LinearMap.ker Lf := by
    intro c hc
    rw [LinearMap.mem_ker, hLe, Finsupp.linearCombination_apply, Finsupp.sum] at hc
    rw [LinearMap.mem_ker, hLf, Finsupp.linearCombination_apply, Finsupp.sum]
    exact lc_zero_of_gram c.support c (veC n mu) (vfC n lam f) _ hK hc
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend
    (((LinearMap.ker Le).liftQ Lf hker).comp (Le.quotKerEquivRange.symm : LinearMap.range Le →ₗ[ℂ] _))
  have hφv : ∀ c, φ (Le c) = Lf c := by
    intro c
    have h1 := LinearMap.congr_fun hφ ⟨Le c, LinearMap.mem_range_self Le c⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply] at h1
    exact h1

  have hrange : LinearMap.range Le = nablaSq ℂ n mu := by
    rw [hLe, Finsupp.range_linearCombination]
    have hle : Submodule.span ℂ (Set.range (veC n mu)) ≤ nablaSq ℂ n mu :=
      Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact (he n mu).2.2 g _ heM)
    have hst : ∀ g : GL (Fin n) ℂ, ∀ x ∈ Submodule.span ℂ (Set.range (veC n mu)),
        sqAct ℂ n mu g x ∈ Submodule.span ℂ (Set.range (veC n mu)) := by
      intro g x hx
      have : Submodule.span ℂ (Set.range (veC n mu)) ≤
          (Submodule.span ℂ (Set.range (veC n mu))).comap (sqLC n mu g) := by
        rw [Submodule.span_le]
        rintro _ ⟨g', rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, sqLC_apply]
        exact Submodule.subset_span ⟨g * g', by simp only [veC, sqAct_mulC]⟩
      exact this hx
    rcases (h n mu).2.1 _ hle hst with h0 | h1
    · exfalso
      apply heN
      have : extremal ℂ n mu ∈ Submodule.span ℂ (Set.range (veC n mu)) :=
        Submodule.subset_span ⟨1, by simp only [veC, sqAct_oneC]⟩
      rw [h0] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exact h1
  have hfL : ∀ c, Lf c ∈ nablaSq ℂ (n + 1) lam := by
    intro c
    have : Lf c ∈ Submodule.span ℂ (Set.range (vfC n lam f)) := by
      rw [← Finsupp.range_linearCombination, ← hLf]
      exact LinearMap.mem_range_self _ c
    exact Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact (he (n + 1) lam).2.2 _ f hf) this
  have hLe_g : ∀ (g : GL (Fin n) ℂ) c, sqAct ℂ n mu g (Le c) = Le (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    have hfun : (⇑(sqLC n mu g) ∘ veC n mu) = (veC n mu ∘ (g * ·)) := by
      funext g'
      simp only [Function.comp_apply, sqLC_apply, veC, sqAct_mulC]
    rw [hLe, Finsupp.linearCombination_mapDomain, ← sqLC_apply, Finsupp.apply_linearCombination, hfun]
  have hLf_g : ∀ (g : GL (Fin n) ℂ) c, sqAct ℂ (n + 1) lam (PI.embGL ℂ n (n + 1) rfl g) (Lf c) =
      Lf (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    have hfun : (⇑(sqLC (n + 1) lam (PI.embGL ℂ n (n + 1) rfl g)) ∘ vfC n lam f) = (vfC n lam f ∘ (g * ·)) := by
      funext g'
      simp only [Function.comp_apply, sqLC_apply, vfC, map_mul, sqAct_mulC]
    rw [hLf, Finsupp.linearCombination_mapDomain, ← sqLC_apply, Finsupp.apply_linearCombination, hfun]
  refine ⟨φ, ⟨fun s hs => ?_, fun g s hs => ?_⟩, ?_⟩
  · rw [← hrange] at hs
    obtain ⟨c, rfl⟩ := hs
    rw [hφv]
    exact hfL c
  · rw [← hrange] at hs
    obtain ⟨c, rfl⟩ := hs
    rw [hLe_g, hφv, hφv, hLf_g]
  · have h1 : extremal ℂ n mu = Le (Finsupp.single 1 1) := by
      rw [hLe, Finsupp.linearCombination_single, one_smul]
      simp only [veC, sqAct_oneC]
    rw [h1, hφv, hLf, Finsupp.linearCombination_single, one_smul]
    simp only [vfC, map_one, sqAct_oneC]
end PI.WGB
