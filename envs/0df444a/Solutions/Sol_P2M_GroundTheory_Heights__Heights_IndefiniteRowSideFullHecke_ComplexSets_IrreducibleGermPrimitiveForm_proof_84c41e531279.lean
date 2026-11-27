-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IrreducibleGermPrimitiveForm_proof_84c41e531279
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:22.152478+00:00
-- url     : https://prove2.me/submissions/74307591-0340-421e-bfe7-0325566b8842

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermPrimitiveForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_primitive_with_resultant_denominator_cfd22a00b3ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germOf_germRep_86925addb537
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germOf_eq_zero_906cfc6a939a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_of_germ_eq_b6b3c7fcfce8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coe_eval__map_74b9cdedd646
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval__monic_apply_f1487d82a379
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval__sum_apply_fd98d3cc73d4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace IrreducibleGermPrimitiveForm
theorem _root_.solution (hF : FiniteFibreGermIntegral.Statement)
    (hZ : ZariskiAnalyticNormality.Statement)
    (hG : GroundTheory.Heights₂.Heights.ComplexSets.GenericPrimitive.Statement)
    (hD : GroundTheory.Heights₂.Heights.ComplexSets.DiscrAdjoin.Statement) :
    IrreducibleGermPrimitiveForm.Statement := by
  intro σ _ X x d A hXan hirr hiso hinj

  have hZ0 := hZ (Fin d) ⊥ (A x) Ideal.isPrime_bot
    (IsIntegrallyClosed.of_equiv (RingEquiv.quotientBot (MvPolynomial (Fin d) ℂ)).symm)
    (fun q hq => by rw [(Ideal.mem_bot).1 hq, map_zero])
  rw [Ideal.map_bot] at hZ0
  obtain ⟨hprime, hnormal⟩ := hZ0
  have : IsDomain (holGerms (A x) ⧸ (⊥ : Ideal (holGerms (A x)))) := Ideal.Quotient.isDomain _
  have : IsDomain (holGerms (A x)) :=
    Function.Injective.isDomain (RingEquiv.quotientBot (holGerms (A x))).symm (RingEquiv.injective _)
  have : IsIntegrallyClosed (holGerms (A x)) := IsIntegrallyClosed.of_equiv (RingEquiv.quotientBot _)

  have : (𝓝[X] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hirr.1)
  have germ_zero : ∀ f : (σ → ℂ) → ℂ, (∀ᶠ z in 𝓝 x, z ∈ X → f z = 0) →
      (f : Germ (𝓝[X] x) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) :=
    fun f h => Germ.coe_eq.2 (eventually_nhdsWithin_iff.2 h)
  have : NoZeroDivisors (germsAlong X x) := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    have h0 : ((f * g : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) := by
      rw [Germ.coe_mul, hfa, hgb]
      exact congrArg Subtype.val hab
    rcases hirr.2 f g hf hg ((eventually_of_germ_eq h0).mono fun z hz hzX => by simpa using hz hzX) with h | h
    · left
      apply Subtype.ext
      rw [← hfa]
      exact germ_zero f h
    · right
      apply Subtype.ext
      rw [← hgb]
      exact germ_zero g h
  have : IsDomain (germsAlong X x) := NoZeroDivisors.to_isDomain _

  let _ : Algebra (holGerms (A x)) (germsAlong X x) := (alongPull X x A).toAlgebra
  have hα : Function.Injective (algebraMap (holGerms (A x)) (germsAlong X x)) := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ
    obtain ⟨h, hh, hφh⟩ := φ.2
    have h1 : ((h ∘ A : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) := by
      have h2 := congrArg Subtype.val hφ
      change (φ.1 : Germ (𝓝 (A x)) ℂ).compTendsto A (tendsto_nhdsWithin_linear A X x) =
        (0 : Germ (𝓝[X] x) ℂ) at h2
      rw [← hφh] at h2
      exact h2
    have h3 := hinj h hh ((eventually_of_germ_eq h1).mono fun z hz hzX => hz hzX)
    apply Subtype.ext
    rw [← hφh]
    exact Germ.coe_eq.2 h3
  have : Algebra.IsIntegral (holGerms (A x)) (germsAlong X x) := by
    refine ⟨fun s => ?_⟩
    obtain ⟨g, hg, hgs⟩ := s.2
    have hs : s = alongOf X x ⟨g, hg⟩ := Subtype.ext hgs.symm
    obtain ⟨M, b, hb, hev⟩ := hF σ X x d A hXan hiso g hg
    let bt : Fin M → analyticAtRing (A x) := fun j => ⟨b j, hb j⟩
    refine ⟨(Polynomial.X ^ M + ∑ j, C (bt j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x)),
      (monic_X_pow_add (degree_sum_fin_lt _)).map _, ?_⟩
    apply Subtype.ext
    rw [hs]
    change ((eval₂ (alongPull X x A) (alongOf X x ⟨g, hg⟩)
      ((Polynomial.X ^ M + ∑ j, C (bt j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x))) : germsAlong X x) : Germ (𝓝[X] x) ℂ) =
        ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ)
    rw [coe_eval₂_map]
    refine germ_zero _ (hev.mono fun z hz hzX => ?_)
    rw [eval₂_monic_apply]
    exact hz hzX

  let c : ℂ →+* holGerms (A x) := (germOf (A x)).comp (constAn (A x))
  let e := Fintype.equivFin σ
  let coord : σ → analyticAtRing x := fun i =>
    ⟨fun w => w i, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt x⟩
  obtain ⟨cc, p, hpm, hpos, hroot, hres0, hq⟩ :=
    primitive_with_resultant_denominator hG hD hα c (fun j => alongOf X x (coord (e.symm j)))
  let ℓ : (σ → ℂ) →L[ℂ] ℂ := ∑ j, cc j • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm j)
  have hℓs : ∑ j, algebraMap (holGerms (A x)) (germsAlong X x) (c (cc j)) * alongOf X x (coord (e.symm j)) =
      alongOf X x ⟨ℓ, ℓ.analyticAt x⟩ := by
    have h1 : ∀ j, algebraMap (holGerms (A x)) (germsAlong X x) (c (cc j)) = alongOf X x (constAn x (cc j)) :=
      fun j => rfl
    simp only [h1, ← map_mul, ← map_sum]
    congr 1
    apply Subtype.ext
    funext w
    simp [ℓ, coord, constAn]
  rw [hℓs] at hroot hq
  set N := p.natDegree with hN
  let a : Fin N → analyticAtRing (A x) := fun j => germRep (A x) (p.coeff j)
  have hPt : (Polynomial.X ^ N + ∑ j, C (a j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x)) = p := by
    conv_rhs => rw [hpm.as_sum]
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C, a, germOf_germRep]
    rw [← hN, Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * Polynomial.X ^ i) N]
  set Pt : (analyticAtRing (A x))[X] := Polynomial.X ^ N + ∑ j, C (a j) * Polynomial.X ^ (j : ℕ) with hPtdef
  let res : analyticAtRing (A x) := Pt.resultant (derivative Pt) N (N - 1)
  have hγres : germOf (A x) res = p.resultant (derivative p) N (N - 1) := by
    rw [← resultant_map_map, ← derivative_map, hPt]
  choose f hfdeg hfeq using hq
  let q : σ → Fin N → analyticAtRing (A x) := fun i j => germRep (A x) ((f (e i)).coeff j)
  have hQt : ∀ i, (∑ j, C (q i j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x)) = f (e i) := by
    intro i
    conv_rhs => rw [as_sum_range' (f (e i)) N (hfdeg (e i))]
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, q, germOf_germRep]
    rw [Fin.sum_univ_eq_sum_range (fun k => C ((f (e i)).coeff k) * Polynomial.X ^ k) N]
    simp only [C_mul_X_pow_eq_monomial]
  have hPtdeg : Pt.natDegree ≤ N := by
    rw [hPtdef, natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt _),
      natDegree_X_pow]
  refine ⟨ℓ, N, fun j => (a j).1, res.1, fun i j => (q i j).1, fun j => (a j).2, res.2, fun i j => (q i j).2,
    ?_, ?_, ?_, fun i => ?_⟩
  · intro h
    apply hres0
    rw [← hγres]
    exact (germOf_eq_zero _ _).2 h
  · rw [← hPt] at hroot
    have h1 := congrArg Subtype.val hroot
    change ((eval₂ (alongPull X x A) (alongOf X x ⟨ℓ, ℓ.analyticAt x⟩) (Pt.map (germOf (A x))) :
      germsAlong X x) : Germ (𝓝[X] x) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) at h1
    rw [coe_eval₂_map] at h1
    refine (eventually_of_germ_eq h1).mono fun z hz hzX => ?_
    have h2 := hz hzX
    rw [hPtdef, eval₂_monic_apply] at h2
    exact h2
  · refine Eventually.of_forall fun y hy => ?_
    obtain ⟨u, v, -, -, huv⟩ := exists_mul_add_mul_eq_C_resultant Pt (derivative Pt) hPtdeg
      ((natDegree_derivative_le Pt).trans (Nat.sub_le_sub_right hPtdeg 1)) (Or.inl hpos.ne')
    let ev : analyticAtRing (A x) →+* ℂ :=
      (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y).comp (analyticAtRing (A x)).subtype
    have hmap : Pt.map ev = Polynomial.X ^ N + ∑ j, C ((a j).1 y) * Polynomial.X ^ (j : ℕ) := by
      simp [hPtdef, Polynomial.map_sum, ev]
    have h2 := congrArg (Polynomial.map ev) huv
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, ← derivative_map,
      hmap] at h2
    have hy' : ev res ≠ 0 := hy
    refine ⟨C (ev res)⁻¹ * u.map ev, C (ev res)⁻¹ * v.map ev, ?_⟩
    calc C (ev res)⁻¹ * u.map ev * (Polynomial.X ^ N + ∑ j, C ((a j).1 y) * Polynomial.X ^ (j : ℕ)) +
          C (ev res)⁻¹ * v.map ev * derivative (Polynomial.X ^ N + ∑ j, C ((a j).1 y) * Polynomial.X ^ (j : ℕ)) =
        C (ev res)⁻¹ * ((Polynomial.X ^ N + ∑ j, C ((a j).1 y) * Polynomial.X ^ (j : ℕ)) * u.map ev +
          derivative (Polynomial.X ^ N + ∑ j, C ((a j).1 y) * Polynomial.X ^ (j : ℕ)) * v.map ev) := by ring
      _ = 1 := by rw [h2, ← C_mul, inv_mul_cancel₀ hy', C_1]
  · have h := hfeq (e i)
    rw [← hQt i, ← hγres, e.symm_apply_apply] at h
    have h1 := congrArg Subtype.val h
    change ((eval₂ (alongPull X x A) (alongOf X x ⟨ℓ, ℓ.analyticAt x⟩)
      ((∑ j, C (q i j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x))) : germsAlong X x) : Germ (𝓝[X] x) ℂ) =
        ((res.1 ∘ A * fun w => w i : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) at h1
    rw [coe_eval₂_map] at h1
    refine (eventually_of_germ_eq h1).mono fun z hz hzX => ?_
    have h2 := hz hzX
    rw [eval₂_sum_apply] at h2
    exact h2.symm
end IrreducibleGermPrimitiveForm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
