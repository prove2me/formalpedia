-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MassFinite_good_localGraph_8ee920f7c539
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:20.486127+00:00
-- url     : https://prove2.me/submissions/9171d6c6-73c7-4f9b-8d37-cbe1fadc3402

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.MassFinite
namespace GroundTheory.Heights₂.Heights.MassFinite
theorem _root_.solution {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hb : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j)
    (I₀ : Finset (Fin n)) (hI : I₀.card = d) (P : MvPolynomial (Fin d) ℂ)
    (hP : ∀ y : Fin d → ℂ, eval y P ≠ 0 →
      ∀ x ∈ ComplexSets.fibre J (U.submatrix (I₀.orderEmbOfFin hI) id) y,
        ∃ (U' : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ)) (g : (Fin d → ℂ) → (Fin n → ℂ)),
          IsOpen U' ∧ y ∈ U' ∧ IsOpen V ∧ x ∈ V ∧ DifferentiableOn ℂ g U' ∧ g y = x ∧
          (∀ w ∈ U', U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ g w = w) ∧
          ComplexSets.zeroSet J ∩ V = g '' U') :
    ∀ z ∈ zeroSetEuc J ∩ {z | eval (U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ WithLp.ofLp z) P ≠ 0},
      ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
        (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
          DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧
          (zeroSetEuc J ∩ {z | eval (U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ WithLp.ofLp z) P ≠ 0}) ∩ V =
            g '' Ω := by
  set A := U.submatrix (I₀.orderEmbOfFin hI) id
  set e := I₀.orderIsoOfFin hI
  rintro z ⟨hzZ, hzP⟩
  obtain ⟨U', V, g, hU', -, hV, hzV, hg, -, hAg, hZV⟩ := hP _ hzP (WithLp.ofLp z) ⟨hzZ, rfl⟩
  let σ : (I₀ → ℂ) →L[ℂ] (Fin d → ℂ) := ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (e k)
  have hσ : ∀ w k, σ w k = w (e k) := fun _ _ => rfl
  let L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm
  have hL : ∀ v, L v = WithLp.toLp 2 v := fun _ => rfl
  have hcP : Continuous fun w : Fin d → ℂ => eval w P := MvPolynomial.continuous_eval P
  have hcA : Continuous fun z' : EuclideanSpace ℂ (Fin n) => A *ᵥ WithLp.ofLp z' :=
    (Continuous.matrix_mulVec continuous_const continuous_id).comp (PiLp.continuous_ofLp 2 _)
  refine ⟨σ ⁻¹' (U' ∩ {w | eval w P ≠ 0}),
    {z' | WithLp.ofLp z' ∈ V ∧ eval (A *ᵥ WithLp.ofLp z') P ≠ 0}, fun w => L (g (σ w)),
    (hU'.inter (isOpen_ne_fun hcP continuous_const)).preimage σ.continuous,
    (hV.preimage (PiLp.continuous_ofLp 2 _)).inter (isOpen_ne_fun (hcP.comp hcA) continuous_const),
    ⟨hzV, hzP⟩, L.differentiable.comp_differentiableOn (hg.comp σ.differentiable.differentiableOn
      fun w hw => hw.1), fun w hw => ?_, ?_⟩
  · funext i
    have h1 := congrFun (hAg _ hw.1) (e.symm i)
    simp only [A, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, hσ,
      ← Finset.coe_orderIsoOfFin_apply, e, OrderIso.apply_symm_apply] at h1
    simp only [frameProj, hb, hL]
    simpa using h1
  · ext z'
    constructor
    · rintro ⟨⟨hz'Z, -⟩, hz'V, hz'P⟩
      have hmem : WithLp.ofLp z' ∈ ComplexSets.zeroSet J ∩ V := ⟨hz'Z, hz'V⟩
      rw [hZV] at hmem
      obtain ⟨w0, hw0, hgw0⟩ := hmem
      have hσw : σ (fun i => w0 (e.symm i)) = w0 := by
        funext k
        simp [hσ]
      refine ⟨fun i => w0 (e.symm i), ⟨by rw [hσw]; exact hw0, ?_⟩, ?_⟩
      · rw [Set.mem_ofPred_eq, hσw, ← hAg w0 hw0, hgw0]
        exact hz'P
      · simp only [hσw, hL, hgw0]
    · rintro ⟨w, ⟨hwU, hwP⟩, rfl⟩
      have hmem : g (σ w) ∈ ComplexSets.zeroSet J ∩ V := hZV ▸ ⟨σ w, hwU, rfl⟩
      have hA : A *ᵥ WithLp.ofLp (L (g (σ w))) = σ w := hAg _ hwU
      refine ⟨⟨fun q hq => hmem.1 q hq, ?_⟩, hmem.2, ?_⟩
      · rw [Set.mem_ofPred_eq, hA]
        exact hwP
      · rw [hA]
        exact hwP
end GroundTheory.Heights₂.Heights.MassFinite
