-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_MinkowskiVolumeForm_proof_49d10ac54218
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:50:30.214813+00:00
-- url     : https://prove2.me/submissions/4924dfe7-7490-4219-bd32-422c55655a8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMinkowskiVolumeForm
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Module MeasureTheory Submodule
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace MinkowskiVolumeForm
theorem _root_.solution : MinkowskiVolumeForm.Statement V d := by
  classical
  intro o b lam hlam hmin
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  have hd : finrank ℝ V = d := Fact.out

  have hcomb : ∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨z, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hz : z ≠ 0 := by
      rintro rfl
      simp at hx0
    simpa [← Int.cast_smul_eq_zsmul ℝ] using hmin z hz
  have hdisc : DiscreteTopology (span ℤ (Set.range b)) :=
    DiscreteTopology.of_forall_le_norm hlam fun x hx => hcomb x x.2 (by simpa using hx)
  have hZ : LinearIndependent ℤ b := by
    rw [Fintype.linearIndependent_iff]
    intro z hz
    by_contra hne
    have hz' : z ≠ 0 := fun h => hne (fun i => by simp [h])
    have h1 := hmin z hz'
    have h2 : ∑ i, (z i : ℝ) • b i = 0 := by simpa [Int.cast_smul_eq_zsmul] using hz
    rw [h2, norm_zero] at h1
    linarith
  have hR : LinearIndependent ℝ b := by
    rw [linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hdisc,
      Set.finrank, finrank_span_eq_card hZ]
  have hcard : Fintype.card (Fin d) = finrank ℝ V := by simp [hd]
  let B : Basis (Fin d) ℝ V := Basis.mk hR (hR.span_eq_top_of_card_eq_finrank' hcard).ge
  have hB : ⇑B = b := Basis.coe_mk _ _

  have hF : volume (ZSpan.fundamentalDomain B) = ENNReal.ofReal |o.volumeForm b| := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped B volume), ← o.measure_eq_volume,
      AlternatingMap.measure_parallelepiped, hB]

  let e : OrthonormalBasis (Fin d) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hd)
  set σ : ℝ := lam / Real.sqrt d with hσ
  have hσ0 : 0 ≤ σ := div_nonneg hlam.le (Real.sqrt_nonneg _)
  let φ : V →ₗ[ℝ] (Fin d → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap ∘ₗ e.repr.toLinearEquiv.toLinearMap
  let P : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Ioo (-σ) σ
  let s : Set V := φ ⁻¹' P
  have hs_mem : ∀ v, v ∈ s ↔ ∀ i, |e.repr v i| < σ := by
    intro v
    simp only [s, P, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo, abs_lt]
    rfl
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    rw [hs_mem] at hx ⊢
    intro i
    simpa using hx i
  have hconv : Convex ℝ s := (convex_pi fun _ _ => convex_Ioo _ _).linear_preimage φ
  have hvol : volume s = ENNReal.ofReal (2 * σ) ^ d := by
    have hmp : MeasurePreserving (fun v : V => WithLp.ofLp (e.repr v)) volume volume :=
      (PiLp.volume_preserving_ofLp (Fin d)).comp e.measurePreserving_repr
    rw [show s = (fun v : V => WithLp.ofLp (e.repr v)) ⁻¹' P from rfl,
      hmp.measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  by_contra hlt
  push Not at hlt
  have hlt' : volume (ZSpan.fundamentalDomain B) * 2 ^ finrank ℝ V < volume s := by
    rw [hd]
    have h : ENNReal.ofReal (|o.volumeForm b| * 2 ^ d) < ENNReal.ofReal ((2 * σ) ^ d) := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), mul_pow, mul_comm]
      exact mul_lt_mul_of_pos_left hlt (by positivity)
    rwa [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow (mul_nonneg zero_le_two hσ0),
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← hF, ← hvol] at h
  have hcount : Countable (span ℤ (Set.range B)).toAddSubgroup := by
    change Countable (span ℤ (Set.range B))
    infer_instance
  obtain ⟨⟨x, hxL⟩, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (ZSpan.isAddFundamentalDomain' B volume) hsymm hconv hlt'
  have hx0' : x ≠ 0 := by
    rintro rfl
    exact hx0 rfl
  have h1 : lam ≤ ‖x‖ := hcomb x (by rw [← hB]; exact hxL) hx0'
  have h2 : ‖x‖ < lam := by
    rw [hs_mem] at hxs
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · exact absurd (@Subsingleton.elim _ (finrank_zero_iff.1 (hd.trans hd0)) x 0) hx0'
    · have hσpos : 0 < σ := div_pos hlam (Real.sqrt_pos.2 (by exact_mod_cast hdpos))
      have hsq : (d : ℝ) * σ ^ 2 = lam ^ 2 := by
        rw [hσ, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        field_simp
      rw [← e.repr.norm_map, EuclideanSpace.norm_eq]
      calc Real.sqrt (∑ i, ‖e.repr x i‖ ^ 2) < Real.sqrt (∑ _i : Fin d, σ ^ 2) := by
            apply Real.sqrt_lt_sqrt (by positivity)
            apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, hdpos⟩⟩)
            intro i _
            rw [Real.norm_eq_abs, sq_lt_sq, abs_of_pos hσpos, abs_abs]
            exact hxs i
        _ = lam := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsq,
              Real.sqrt_sq hlam.le]
  linarith
end MinkowskiVolumeForm
end GroundTheory.Heights₂.Heights.FiniteCovolume
