-- Prove2me | solution 1 for PI.LocLatEq.W.coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:50:33.88734+00:00
-- url     : https://prove2.me/submissions/67bca341-d967-44ec-b90b-144815857195

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_EpNontrivial
import Theorems.Thm_PI_LocLatEq_W_ep_nontrivial
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc Polynomial
open PI PI.LocLatEq PI.LocLatEq.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace PI.LocLatEq.W
theorem _root_.solution (h2 : Module.finrank F E = 2) (A : LocAt F E sig p) (a : E)
    (ha : IsIntegral 𝒪[A.Fp] (A.ιE a)) (hnot : a ∉ (algebraMap F E).range) (i : ℕ) :
    A.ιF ((minpoly F a).coeff i) ∈ 𝒪[A.Fp] := by
  classical
  haveI := ep_nontrivial A
  haveI := A.free
  have hli : LinearIndependent F ![(1 : E), a] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro c hc
    apply hnot
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB : ⇑B = ![(1 : E), a] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hspanP : ⊤ ≤ Submodule.span A.Fp (Set.range ![(1 : A.Ep), A.ιE a]) := by
    rw [← A.span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have hx := B.sum_repr x
    rw [hB, Fin.sum_univ_two] at hx
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx
    have : A.ιE x = A.ιF (B.repr x 0) • (1 : A.Ep) + A.ιF (B.repr x 1) • A.ιE a := by
      conv_lhs => rw [← hx]
      simp only [map_add, map_mul, map_one, Algebra.smul_def, A.compat, mul_one]
    rw [SetLike.mem_coe, this]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  have hliP : LinearIndependent A.Fp ![(1 : A.Ep), A.ιE a] :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspanP (by simp [A.rank])
  have hnotP : A.ιE a ∉ (algebraMap A.Fp A.Ep).range := by
    rintro ⟨c, hc⟩
    rw [LinearIndependent.pair_iff' one_ne_zero] at hliP
    apply hliP c
    rw [← hc, Algebra.algebraMap_eq_smul_one]
  haveI : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; norm_num)
  have hintP : IsIntegral A.Fp (A.ιE a) := Algebra.IsIntegral.isIntegral _
  have hdegP : 2 ≤ (minpoly A.Fp (A.ιE a)).natDegree := by
    have h0 := minpoly.natDegree_pos hintP
    have h1 : (minpoly A.Fp (A.ιE a)).natDegree ≠ 1 := fun h => hnotP (minpoly.natDegree_eq_one_iff.mp h)
    omega
  have hintF : IsIntegral F a := Algebra.IsIntegral.isIntegral _
  have hdegF : (minpoly F a).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le a
  set g : A.Fp[X] := (minpoly F a).map A.ιF with hg
  have hgmon : g.Monic := (minpoly.monic hintF).map _
  have hgdeg : g.natDegree ≤ 2 := by
    rw [hg, natDegree_map]
    exact hdegF
  have hgα : aeval (A.ιE a) g = 0 := by
    rw [hg, aeval_def, eval₂_map]
    have hcomp : (algebraMap A.Fp A.Ep).comp A.ιF = A.ιE.comp (algebraMap F E) := by
      ext y
      simp [A.compat]
    rw [hcomp, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hdvd : minpoly A.Fp (A.ιE a) ∣ g := minpoly.dvd A.Fp _ hgα
  have hgeq : g = minpoly A.Fp (A.ιE a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintP) hgmon hdvd (by omega)
  have hdvd2 : minpoly A.Fp (A.ιE a) ∣ (minpoly 𝒪[A.Fp] (A.ιE a)).map (algebraMap 𝒪[A.Fp] A.Fp) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, minpoly.aeval]
  obtain ⟨g', hg'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd A.Fp (minpoly.monic ha) hdvd2
  rw [(minpoly.monic hintP).leadingCoeff, C_1, mul_one] at hg'
  have hc := congrArg (fun q => q.coeff i) (hg'.trans hgeq.symm)
  simp only [coeff_map, hg] at hc
  rw [← hc]
  exact (g'.coeff i).2
end PI.LocLatEq.W
