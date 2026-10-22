-- Prove2me | solution 1 for QAlgorithms.OperatorAlgebra.dual_commutator_coeff_traceclass
-- status  : ACCEPTED   (prove)
-- author  : @Imine
-- created : 2026-10-21T06:01:42.793238+00:00
-- url     : https://prove2.me/submissions/8dc985e4-0de5-448b-b387-14b07dd980fb

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18
noncomputable section
set_option autoImplicit false
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Claimed50.P35 (tracePair)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)
open QAlgorithms.Papers.Independent.Next46.P18 (DualChannel)
attribute [local instance] Classical.propDecidable Classical.decEq

lemma single_factor {I : Type} (i : I) (c : ℂ) :
    (lp.single 2 i c : Hilbert I) = c • (lp.single 2 i 1 : Hilbert I) := by
  ext j
  simp [lp.single_apply, Pi.single_apply]

lemma rank_row_sum {I : Type} (u v : Hilbert I) (D : Hilbert I →L[ℂ] Hilbert I) :
    HasSum (fun a => u a * inner ℂ v (D (lp.single 2 a 1))) (inner ℂ v (D u)) := by
  have hh := (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) u).map
    ((innerSL ℂ v).comp D).toAddMonoidHom
    ((innerSL ℂ v).comp D).continuous
  change HasSum (fun a => inner ℂ v (D (lp.single 2 a (u a)))) (inner ℂ v (D u)) at hh
  convert hh using 1
  funext a
  rw [single_factor a (u a), map_smul, inner_smul_right]

lemma trace_two_rank {I : Type} (u v u' v' : Hilbert I)
    (D : Hilbert I →L[ℂ] Hilbert I) :
    tracePair (fun a b => u a * star (v b) - u' a * star (v' b)) (operatorCoeff D) =
      inner ℂ v (D u) - inner ℂ v' (D u') := by
  have hrow (a : I) :
      (∑' b, (u a * star (v b) - u' a * star (v' b)) * operatorCoeff D b a) =
      u a * inner ℂ v (D (lp.single 2 a 1)) -
      u' a * inner ℂ v' (D (lp.single 2 a 1)) := by
    have h₁ := (lp.summable_inner v (D (lp.single 2 a 1))).mul_left (u a)
    have h₂ := (lp.summable_inner v' (D (lp.single 2 a 1))).mul_left (u' a)
    calc
      _ = ∑' b, (u a * inner ℂ (v b) ((D (lp.single 2 a 1)) b) -
          u' a * inner ℂ (v' b) ((D (lp.single 2 a 1)) b)) := by
        apply tsum_congr
        intro b
        simp only [operatorCoeff, RCLike.inner_apply']
        change (u a * star (v b) - u' a * star (v' b)) * ((D (lp.single 2 a 1)) b) =
          u a * (star (v b) * ((D (lp.single 2 a 1)) b)) -
          u' a * (star (v' b) * ((D (lp.single 2 a 1)) b))
        ring
      _ = _ := by
        rw [h₁.tsum_sub h₂]
        simp only [tsum_mul_left, ← lp.inner_eq_tsum]

  simp only [tracePair, hrow]
  rw [(rank_row_sum u v D).summable.tsum_sub (rank_row_sum u' v' D).summable,
    (rank_row_sum u v D).tsum_eq, (rank_row_sum u' v' D).tsum_eq]

lemma two_rank_traceclass {I : Type} (u v u' v' : Hilbert I) :
    IsTraceClass (fun a b => u a * star (v b) - u' a * star (v' b)) := by
  refine ⟨{left := fun n => if n = 0 then u else if n = 1 then -u' else 0,
           right := fun n => if n = 0 then v else if n = 1 then v' else 0,
           summable := ?_, coefficients := ?_}⟩
  · exact summable_of_ne_finset_zero (s := {0,1}) (by
      intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      simp [hn.1, hn.2])
  · intro a b
    rw [tsum_eq_sum (s := {0,1}) (by
      intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      simp [hn.1, hn.2])]
    simp [sub_eq_add_neg]

theorem solution {I J : Type} (Phi : DualChannel I J)
    (A : Hilbert I →L[ℂ] Hilbert I) (i j : I) :
    ∃ Y : Matrix J J ℂ, IsTraceClass Y ∧ ∀ B : Hilbert J →L[ℂ] Hilbert J,
      operatorCoeff ((Phi.dual B).comp A - A.comp (Phi.dual B)) i j =
        tracePair Y (operatorCoeff B) := by
  let u := A (lp.single 2 j 1)
  let v : Hilbert I := lp.single 2 i 1
  let u' : Hilbert I := lp.single 2 j 1
  let v' := A.adjoint (lp.single 2 i 1)
  let X : Matrix I I ℂ := fun a b => u a * star (v b) - u' a * star (v' b)
  have hX : IsTraceClass X := two_rank_traceclass u v u' v'
  refine ⟨Phi.predual.val X, Phi.predual.property.1 X hX, ?_⟩
  intro B
  rw [Phi.pairing X hX B, trace_two_rank]
  simp only [u, v, u', v', ContinuousLinearMap.adjoint_inner_left,
    lp.inner_single_left, RCLike.inner_apply', operatorCoeff,
    sub_apply, ContinuousLinearMap.comp_apply, lp.coeFn_sub,
    Pi.sub_apply]
  simp
