-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.TB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:22:20.28292+00:00
-- url     : https://prove2.me/submissions/62f56038-77bc-450e-bf1e-8d96a5bf4ad0

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ExistsDoubledUnitaryBlock
import Theorems.Thm_PositivityTheory_ThKF0_Chr_lev_scalar
import Theorems.Thm_PositivityTheory_ThKF0_Chr_rel_dbl
import Theorems.Thm_PositivityTheory_ThKF0_Chr_exists_doubled_unitary_block
import Theorems.Thm_PositivityTheory_ThKF0_Chr_fac_ne
import Theorems.Thm_PositivityTheory_ThKF0_Chr_blk_val
import Theorems.Thm_PositivityTheory_ThKF0_Chr_det_blk
import Theorems.Thm_P2M_PositivityTheory_ThK_SiegelT_map_mul__f92fda10766b
import Theorems.Thm_P2M_PositivityTheory_ThK_SiegelT_map_one__a6a1ccb9bfd7
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_box_E
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_box_ne
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_comp_ne
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_exists_E
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_exists_diag
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Fr_continuous_emb
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Fr_emb_i
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Fr_embeddingAtLocalFactor
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Fr_exists_gamma
import Theorems.Thm_PositivityTheory_ThKF0_Chr_IsSp_trans
import Theorems.Thm_PositivityTheory_ThKF0_Chr_box_cancel
import Theorems.Thm_PositivityTheory_ThKF0_Chr_box_ne
import Theorems.Thm_PositivityTheory_ThK_SiegelT_exists_gamma
import Theorems.Thm_PositivityTheory_ThK_SiegelT_rule_of_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT
variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β β₁ ν κ κ₁ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁]
  [Fintype ν] [DecidableEq ν] [Fintype κ] [Fintype κ₁] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {ι : Matrix β β₁ E} {X : Matrix β ν E}
  {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution [TopologicalSpace R] [TopologicalSpace E] [IsModuleTopology R E] [IsTopologicalRing E]
    (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e)
    {η : ℤˣ} {Y : Matrix β ν E} {π : Matrix β₁ β E} {ρ : Matrix (ν ⊕ ν) β E} (hF : Fr c J J₁ (hyp ν η) ι (fromCols X Y) π ρ)
    {d : Darboux (symp c ξ JA J) κ} {d₁ : Darboux (symp c ξ JA J₁) κ₁}
    (hrel : ∀ u z, Rel S j (d.e u) (d₁.e z) ↔ ∃ a : Matrix α ν E, u = z * ιᵀ + a * Xᵀ) {χ : Eˣ →* Circle}
    {om : UG c J →* Module.End ℂ ((κ → R) → ℂ)} {om₁ : UG c J₁ →* Module.End ℂ ((κ₁ → R) → ℂ)}
    (hW : IsUWeilB c C ψ ξ JA J d χ om) (hW₁ : IsUWeilB c C ψ ξ JA J₁ d₁ χ om₁)
    (hch : ∀ a : UG c (dbl J₁) →* ℂˣ, Continuous a → (∀ (p : UG c (dbl J₁)) (t : GL β₁ E),
      p.1.1 * diagCols (E := E) β₁ = diagCols (E := E) β₁ * t.1 → a p = 1) → a = 1)
    (m : UG c J) (g : UG c J₁) (t : GL ν E) (h1 : m.1.1 * ι = ι * g.1.1) (h2 : m.1.1 * X = X * t.1) :
    ∀ φ ∈ C.sp κ, e (om m φ) = fac C χ (Fintype.card α) (GeneralLinearGroup.det t) • om₁ g (e φ) := by
  obtain ⟨hs₀, dd, omd, hd, ⟨-, hs, hr⟩, hb⟩ := hW
  obtain ⟨hs₁₀, dd₁, omd₁, hd₁, ⟨-, hs₁, hr₁⟩, hb₁⟩ := hW₁
  have hj2 := hj.sumMap hj
  have hrel2 := rel_dbl hj hrel hd hd₁
  obtain ⟨E₂, hE⟩ := h.exists_E hS.dbS hj2
  obtain ⟨l, hl, hinv, hcyc⟩ := h.exists_diag κ₁
  obtain ⟨γ, s, s', e1, e2, hγ⟩ := hF.exists_gamma
  have hrule := rule_of_conj hs.toIsSplitting γ s s' e1 e2 hγ hr
  have hdiag : ∀ z : Matrix α β₁ E, dd₁.e (z * (diagCols (E := E) β₁)ᵀ) = dv (d₁.e z) (d₁.e z) := fun z => by
    rw [diagCols, transpose_fromRows, transpose_one, mul_fromCols, Matrix.mul_one, hd₁]
    rfl
  have hL := hrule (l ∘ₗ E₂) (hE.adm l hl) fun z φ hφ => by
    have r := (hrel2 (z * (fromCols (dd2 ι * diagCols (E := E) β₁) (dd2 X))ᵀ) (z.toCols₁ * (diagCols (E := E) β₁)ᵀ)).2
      ⟨z.toCols₂, by
        conv_lhs => rw [← fromCols_toCols z]
        rw [transpose_fromCols, fromCols_mul_fromRows, transpose_mul, Matrix.mul_assoc]⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Darboux.rho, hE.law _ _ r _ hφ, hdiag, hinv _ _ (hE.maps _ hφ)]
  have hL₁ := hr₁ l hl fun z φ hφ => by rw [Darboux.rho, hdiag, hinv _ _ hφ]
  obtain ⟨Ψ₀, hΨ₀, hne⟩ := h.comp_ne hS.dbS hj2 hE hcyc
  have hE0 : E₂ Ψ₀ ≠ 0 := fun e0 => hne (by rw [e0, map_zero])
  let em : UG c (dbl J₁) →* UG c (dbl J) := hF.dbl.emb.comp (MonoidHom.inl _ _)
  have emi : ∀ p, (em p).1.1 * dd2 ι = dd2 ι * p.1.1 := fun p => hF.dbl.emb_i (p, 1)
  have emx : ∀ p, (em p).1.1 * dd2 X = dd2 X * (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E) := fun p => by
    have e3 : dd2 (fromCols X Y) * dd2 (fromRows (1 : Matrix ν ν E) (0 : Matrix ν ν E)) = dd2 X := by
      rw [fromBlocks_multiply]
      simp [fromCols_mul_fromRows]
    have e4 : (em p).1.1 * dd2 (fromCols X Y) = dd2 (fromCols X Y) * (1 : Matrix ((ν ⊕ ν) ⊕ (ν ⊕ ν)) ((ν ⊕ ν) ⊕ (ν ⊕ ν)) E) :=
      hF.dbl.embeddingAtLocalFactor (p, 1)
    rw [← e3, ← Matrix.mul_assoc, e4, Matrix.mul_one, Matrix.mul_one]
  choose a ha using fun p => lev_scalar h hS.dbS hj2 hE hrel2 hs.toIsSplitting hs₁.toIsSplitting (em p) p 1 (emi p) (emx p)
  have hinj : ∀ p, ∀ Ψ, omd₁ p Ψ = 0 → Ψ = 0 := fun p Ψ h0 => by
    have := congrArg (omd₁ p⁻¹) h0
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at this
  let A : UG c (dbl J₁) →* ℂ :=
    { toFun := a
      map_one' := by
        have := ha 1 Ψ₀ hΨ₀
        rw [map_one, map_one, map_one, Module.End.one_apply, Module.End.one_apply] at this
        exact smul_left_injective ℂ hE0 (this.symm.trans (one_smul _ _).symm)
      map_mul' := fun p q => by
        have := ha (p * q) Ψ₀ hΨ₀
        rw [map_mul, map_mul, Module.End.mul_apply, ha p _ (hs.pres _ _ hΨ₀), ha q _ hΨ₀, map_smul, smul_smul,
          ← Module.End.mul_apply, ← map_mul] at this
        exact smul_left_injective ℂ (fun e0 => hE0 (hinj _ _ e0)) this.symm }
  have hA : A.toHomUnits = 1 := hch _ (by
    rw [Units.isEmbedding_val₀.continuous_iff]
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    obtain ⟨w, hw⟩ := hcyc _ (hs₁.pres p₀ _ (hE.maps _ hΨ₀)) fun e0 => hE0 (hinj _ _ e0)
    obtain ⟨z, rfl⟩ := dd₁.e.surjective w
    have r := (hrel2 (actB c p₀⁻¹ z * (dd2 ι)ᵀ) (actB c p₀⁻¹ z)).2 ⟨0, by simp⟩
    have hΨ := h.schr _ (dd.e (actB c p₀⁻¹ z * (dd2 ι)ᵀ)) _ hΨ₀
    have h0 : l (omd₁ p₀ (E₂ (schr ψ (dd.e (actB c p₀⁻¹ z * (dd2 ι)ᵀ)) Ψ₀))) ≠ 0 := by
      rw [hE.law _ _ r _ hΨ₀]
      have := hs₁.impl p₀ (actB c p₀⁻¹ z) _ (hE.maps _ hΨ₀)
      rw [show actB c p₀ (actB c p₀⁻¹ z) = z by simp [actB, Matrix.mul_assoc, ← transpose_mul]] at this
      exact fun e0 => hw ((congrArg l this).symm.trans e0)
    generalize schr ψ (dd.e (actB c p₀⁻¹ z * (dd2 ι)ᵀ)) Ψ₀ = Ψ at hΨ h0
    have c1 := (hs.cont _ (hE.adm l hl) Ψ hΨ).comp hF.dbl.continuous_emb
    have c2 := hs₁.cont l hl _ (hE.maps Ψ hΨ)
    refine (c1.continuousAt.div c2.continuousAt h0).congr ?_
    filter_upwards [c2.continuousAt.eventually_ne h0] with p hp
    show l (E₂ (omd (em p) Ψ)) / _ = a p
    rw [ha p Ψ hΨ, map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hp]) fun p t' hp => by
    have e3 := hL (em p) (blk t' (1 : GL (ν ⊕ ν) E)) (by
      rw [blk_val, mul_fromCols, fromCols_mul_fromBlocks, ← Matrix.mul_assoc, emi, emx, Matrix.mul_assoc, hp]
      simp [Matrix.mul_assoc]) Ψ₀ hΨ₀
    rw [det_blk, map_one, mul_one, LinearMap.comp_apply, LinearMap.comp_apply, ha p _ hΨ₀, map_smul,
      hL₁ p t' hp _ (hE.maps _ hΨ₀), smul_eq_mul] at e3
    exact Units.ext ((mul_eq_right₀ (mul_ne_zero (fac_ne χ _ _) hne)).1 e3)
  have ha1 : ∀ p, ∀ Ψ ∈ C.sp (κ ⊕ κ), E₂ (omd (em p) Ψ) = omd₁ p (E₂ Ψ) := fun p Ψ hΨ => by
    have : a p = 1 := congrArg Units.val (DFunLike.congr_fun hA p)
    rw [ha p Ψ hΨ, this, one_smul]
  obtain ⟨md, hmd⟩ := exists_doubled_unitary_block m
  obtain ⟨gd, hgd⟩ := exists_doubled_unitary_block g
  have k1 : md.1.1 * dd2 ι = dd2 ι * gd.1.1 := by
    rw [hmd, hgd, fromBlocks_multiply, fromBlocks_multiply]; simp [h1]
  have k2 : md.1.1 * dd2 X = dd2 X * (blk t (1 : GL ν E)).1 := by
    rw [blk_val, hmd, fromBlocks_multiply, fromBlocks_multiply]; simp [h2]
  have k3 : (md * em gd⁻¹).1.1 * dd2 ι = dd2 ι * (1 : UG c (dbl J₁)).1.1 := by
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, emi, ← Matrix.mul_assoc, k1, Matrix.mul_assoc]
    simp
  have k4 : (md * em gd⁻¹).1.1 * dd2 X = dd2 X * (blk t (1 : GL ν E)).1 := by
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, emx, Matrix.mul_one, k2]
  obtain ⟨b, hb'⟩ := lev_scalar h hS.dbS hj2 hE hrel2 hs.toIsSplitting hs₁.toIsSplitting _ 1 _ k3 k4
  have hbv : b = fac C χ (Fintype.card α) (GeneralLinearGroup.det t) := by
    have e3 := hL (md * em gd⁻¹) (blk (1 : GL β₁ E) (blk t (1 : GL ν E))) (by
      rw [blk_val 1, mul_fromCols, fromCols_mul_fromBlocks, ← Matrix.mul_assoc, k3, k4]
      simp) Ψ₀ hΨ₀
    rw [det_blk, det_blk, map_one, map_one, mul_one, one_mul, LinearMap.comp_apply, LinearMap.comp_apply, hb' _ hΨ₀, map_one,
      Module.End.one_apply, map_smul, smul_eq_mul] at e3
    exact mul_right_cancel₀ hne e3
  obtain ⟨φ₁, h₁, φ₂, h₂, hne₂⟩ := h.box_ne hS hj hE hcyc
  obtain ⟨B, hB, hBe⟩ := h.box_E hS hj he hE φ₂ h₂
  have hB0 : B ≠ 0 := fun e0 => hne₂ (by
    rw [hBe _ h₁, e0, show boxFun (e φ₁) (0 : (κ₁ → R) → ℂ) = 0 from funext fun x => mul_zero _, map_zero])
  intro φ hφ
  have hx := h.box _ _ _ hφ _ h₂
  have e5 : omd md (boxFun φ φ₂) = omd (md * em gd⁻¹) (omd (em gd) (boxFun φ φ₂)) := by
    rw [← Module.End.mul_apply, ← map_mul, map_inv, inv_mul_cancel_right]
  have e6 := congrArg E₂ e5
  rw [hb' _ (hs.pres _ _ hx), map_one, Module.End.one_apply, ha1 _ _ hx, hb m md hmd _ hφ _ h₂, hBe _ (hs₀.pres _ _ hφ),
    hBe _ hφ, hb₁ g gd hgd _ (he.maps _ hφ) _ hB, hbv] at e6
  exact box_cancel hB0 (e6.trans (funext fun x => (mul_assoc _ _ _).symm))
end PositivityTheory.ThKF0.Chr
