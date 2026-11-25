-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramMatrixExistence.Q_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:04:40.566792+00:00
-- url     : https://prove2.me/submissions/86563832-3ba2-46bd-97f7-ddc5cd353e48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpComponentCombination
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramMatrixExistence
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_smul_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthogonalComplementLines_ppos_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpComponentCombination_uc_comb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpComponentCombination_uc_perp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_Sform_h
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_detG_ne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


section
namespace ReciprocityTheory.ChartRestriction.G.FD.GramMatrixExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
  ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
private lemma hermC_sub_smul_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (u w v : Fin r → ℂ) (a : ℂ) :
    hermC τ G (u - a • w) v = hermC τ G u v - a * hermC τ G w v := by
  unfold hermC
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
private lemma hermC_smul_left_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (u v : Fin r → ℂ) (a : ℂ) :
    hermC τ G (a • u) v = a * hermC τ G u v := by
  have h := hermC_sub_smul_left τ G 0 u v (-a)
  have h0 : hermC τ G 0 v = 0 := by simp [hermC]
  simpa [h0] using h
private lemma hermC_sum_smul_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ}
    (a : Fin n → ℂ) (g : Fin n → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ j, a j • g j) w = ∑ j, a j * hermC τ G (g j) w := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
private lemma hermC_sum_smul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ}
    (u : Fin r → ℂ) (b : Fin n → ℂ) (g : Fin n → Fin r → ℂ) :
    hermC τ G u (∑ l, b l • g l) = ∑ l, conj (b l) * hermC τ G u (g l) := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring
private lemma herm_eq_hermC_emb_emb (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    τ (herm G x y) = hermC τ G (Data.emb τ x) (Data.emb τ y) := by
  simp only [herm, hermC, map_sum, map_mul, Data.emb, cc, IsCMField.complexEmbedding_complexConj]
private lemma emb_sum_smul' (τ : E →+* ℂ) {n : ℕ} (c : Fin n → E) (β : Fin n → Fin r → E) :
    Data.emb τ (∑ k, c k • β k) = ∑ k, τ (c k) • Data.emb τ (β k) := by
  funext a
  simp [Data.emb, Finset.sum_apply, map_sum, map_mul]
end
end ReciprocityTheory.ChartRestriction.G.FD.GramMatrixExistence
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramMatrixExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
  ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.GramMatrixExistence
theorem _root_.solution (X : DataX E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r)
    (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hf : X.UBasis z0 ξ f)
    (β : Fin (r - 2) → Fin r → E) (hβξ : ∀ k, herm X.Gm (β k) ξ = 0)
    (hli : LinearIndependent E (Fin.cons ξ β : Fin (r - 2 + 1) → Fin r → E))
    (hspan : ∀ x : Fin r → E, herm X.Gm x ξ = 0 →
      ∃ (c : Fin (r - 2) → E) (e : E), x = ∑ k, c k • β k + e • ξ) :
    ∃ Q : X.Ψ → Matrix (Fin (r - 2)) (Fin (r - 2)) ℂ, (∀ τ, (Q τ).det ≠ 0) ∧
      (∀ τ (c c' : Fin (r - 2) → E), τ.1 ((Sform X β).h c c') =
        ReciprocityTheory.MultiplicativeHeights.jForm (X.p0 - 1) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c)
          (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c')) ∧
      (∀ τ (c : Fin (r - 2) → E), X.ucomp z0 ξ (X.embV (∑ k, c k • β k)) τ =
        ∑ k, (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) k • f τ k) := by
  classical
  have hξξ : herm X.Gm ξ ξ = 0 := hξ.2.1
  have hξ0 : ξ ≠ 0 := hξ.2.2
  have he0 : ∀ τ : X.Ψ, Data.emb τ.1 ξ ≠ 0 := by
    intro τ h
    apply hξ0
    funext a
    have h1 := congrFun h a
    simp only [Data.emb, Pi.zero_apply, map_eq_zero] at h1
    simpa using h1
  have hHf : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    intro τ
    rw [Data.Hf_self X.toData hz]
    exact_mod_cast (Data.maj_pos X.toData hz τ (he0 τ)).ne'
  have hperp : ∀ (τ : X.Ψ) (y : Fin r → E), herm X.Gm y ξ = 0 →
      hermC τ.1 X.Gm (Data.emb τ.1 y) (Data.emb τ.1 ξ) = 0 := by
    intro τ y hy
    rw [← herm_eq_hermC_emb_emb, hy, map_zero]
  have hee : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 :=
    fun τ => hperp τ ξ hξξ
  have huc : ∀ (τ : X.Ψ) (v : Fin r → E),
      X.ucomp z0 ξ (X.embV v) τ = uc X.toData z0 ξ τ (Data.emb τ.1 v) := fun τ v => rfl
  have hmem : ∀ (τ : X.Ψ) (v : Fin r → ℂ), hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0 →
      uc X.toData z0 ξ τ v ∈ Submodule.span ℂ (Set.range (f τ)) := by
    intro τ v hv
    set e := Data.emb τ.1 ξ with he
    set t := X.Hf z0 τ v e / X.Hf z0 τ e e with ht
    have hu : uc X.toData z0 ξ τ v = v - t • e := rfl
    have h1 : hermC τ.1 X.Gm (uc X.toData z0 ξ τ v) e = 0 := by
      rw [hu, hermC_sub_smul_left, hv, hee τ]
      ring
    have h2 : X.Hf z0 τ (uc X.toData z0 ξ τ v) e = 0 := by
      have hl : (2 : ℂ) • X.ppos z0 τ (v - t • e) - (v - t • e) =
          ((2 : ℂ) • X.ppos z0 τ v - v) - t • ((2 : ℂ) • X.ppos z0 τ e - e) := by
        rw [ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines.ppos_sub X.toData, Data.ppos_smul_eq]
        module
      have hd : X.Hf z0 τ (uc X.toData z0 ξ τ v) e =
          X.Hf z0 τ v e - t * X.Hf z0 τ e e := by
        rw [hu]
        show hermC τ.1 X.Gm ((2 : ℂ) • X.ppos z0 τ (v - t • e) - (v - t • e)) e = _
        rw [hl, hermC_sub_smul_left]
        rfl
      rw [hd, ht, div_mul_cancel₀ _ (hHf τ), sub_self]
    have h3 : hermC τ.1 X.Gm (X.Jt z0 τ (uc X.toData z0 ξ τ v)) e = 0 := by
      show hermC τ.1 X.Gm (I • ((2 : ℂ) • X.ppos z0 τ (uc X.toData z0 ξ τ v) -
        uc X.toData z0 ξ τ v)) e = 0
      rw [hermC_smul_left_mul]
      change I * X.Hf z0 τ (uc X.toData z0 ξ τ v) e = 0
      rw [h2, mul_zero]
    exact (hf τ).2.2.2.2 _ h1 h3
  have hcoord : ∀ (τ : X.Ψ) (w : Fin r → ℂ), w ∈ Submodule.span ℂ (Set.range (f τ)) →
      w = ∑ j : Fin (r - 2), ((if (j : ℕ) < X.p0 - 1 then (1 : ℂ) else -1) * hermC τ.1 X.Gm w (f τ j)) • f τ j := by
    intro τ w hw
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hw
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [hermC_sum_smul_left]
    simp_rw [(hf τ).2.2.1]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    split_ifs <;> ring
  let Q : X.Ψ → Matrix (Fin (r - 2)) (Fin (r - 2)) ℂ := fun τ => Matrix.of fun j k =>
    (if (j : ℕ) < X.p0 - 1 then (1 : ℂ) else -1) *
      hermC τ.1 X.Gm (uc X.toData z0 ξ τ (Data.emb τ.1 (β k))) (f τ j)
  have hb : ∀ (τ : X.Ψ) (k : Fin (r - 2)),
      uc X.toData z0 ξ τ (Data.emb τ.1 (β k)) = ∑ j, Q τ j k • f τ j := by
    intro τ k
    exact hcoord τ _ (hmem τ _ (hperp τ _ (hβξ k)))
  have hQf : ∀ τ (c : Fin (r - 2) → E), X.ucomp z0 ξ (X.embV (∑ k, c k • β k)) τ =
      ∑ k, (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) k • f τ k := by
    intro τ c
    rw [huc, emb_sum_smul', uc_comb (X := X.toData) (z0 := z0) (ξ := ξ) (τ := τ) hz]
    simp_rw [hb τ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mulVec, dotProduct, ReciprocityTheory.MultiplicativeHeights.embVec, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hp : ∀ (τ : X.Ψ) (c : Fin (r - 2) → E),
      hermC τ.1 X.Gm (Data.emb τ.1 (∑ k, c k • β k)) (Data.emb τ.1 ξ) = 0 := by
    intro τ c
    rw [emb_sum_smul', hermC_sum_smul_left]
    simp [hperp τ _ (hβξ _)]
  have hSQ : ∀ τ (c c' : Fin (r - 2) → E), τ.1 ((Sform X β).h c c') =
      ReciprocityTheory.MultiplicativeHeights.jForm (X.p0 - 1) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c)
        (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c') := by
    intro τ c c'
    rw [Sform_h, herm_eq_hermC_emb_emb, ← uc_perp (X := X.toData) (z0 := z0) (ξ := ξ) (τ := τ) (hee τ)
      (Data.emb τ.1 (∑ k, c k • β k)) (Data.emb τ.1 (∑ k, c' k • β k)) (hp τ c) (hp τ c'),
      ← huc, ← huc, hQf, hQf, hermC_sum_smul_left]
    simp_rw [hermC_sum_smul_right, (hf τ).2.2.1]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    unfold ReciprocityTheory.MultiplicativeHeights.jForm ReciprocityTheory.MultiplicativeHeights.sgn
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  refine ⟨Q, ?_, hSQ, hQf⟩
  intro τ hdet
  apply detG_ne (X := X) (ξ := ξ) (β := β) hξ hβξ hli hspan
  have hmap : τ.1.mapMatrix (Sform X β).G = (Q τ)ᴴ *
      Matrix.diagonal (fun k : Fin (r - 2) => ReciprocityTheory.MultiplicativeHeights.sgn (X.p0 - 1) k) * Q τ := by
    ext a b
    have h := hSQ τ (Pi.single a 1) (Pi.single b 1)
    have hh : (Sform X β).h (Pi.single a 1) (Pi.single b 1) = (Sform X β).G a b := by
      simp [ReciprocityTheory.MultiplicativeHeights.HermForm.h, Pi.single_apply, apply_ite, ite_mul, mul_ite]
    have hs : ∀ a : Fin (r - 2), ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (Pi.single a (1 : E)) = Pi.single a 1 := by
      intro a
      funext i
      by_cases hi : i = a
      · subst hi; simp [ReciprocityTheory.MultiplicativeHeights.embVec]
      · simp [ReciprocityTheory.MultiplicativeHeights.embVec, hi]
    rw [hh, hs, hs, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, h]
    simp [ReciprocityTheory.MultiplicativeHeights.jForm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hdm := RingHom.map_det τ.1 (Sform X β).G
  rw [hmap, Matrix.det_mul, Matrix.det_mul, hdet, mul_zero] at hdm
  exact (map_eq_zero τ.1).1 hdm
end ReciprocityTheory.ChartRestriction.G.FD.GramMatrixExistence
