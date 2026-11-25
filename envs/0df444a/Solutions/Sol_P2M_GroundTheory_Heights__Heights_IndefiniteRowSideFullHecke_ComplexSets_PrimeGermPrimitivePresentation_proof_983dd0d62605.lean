-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermPrimitivePresentation_proof_983dd0d62605
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:35:53.23896+00:00
-- url     : https://prove2.me/submissions/a5681a33-3247-4c72-b404-3a7a45b9fc80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermCentredIntegralEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermPrimitivePresentation_pull_toGerm_8762c4c475dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermPrimitivePresentation_toGerm_mem_iff_9b3ec135511e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_exists_primitive_data_34d085bb3e1a


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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermPrimitivePresentation
variable {σ : Type} [Fintype σ]
set_option maxHeartbeats 2000000
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermPrimitivePresentation
theorem _root_.solution (hFP : PrimeGermFiniteProjection.Statement) (hIC : HolGermsIntegrallyClosed.Statement)
    (hCE : CentredIntegralEquation.Statement) : PrimeGermPrimitivePresentation.Statement := by
  classical
  intro σ _ w k p hp hPr
  obtain ⟨d, A, hinj, hint, hgen⟩ := hFP σ w k p hp hPr
  obtain ⟨hdom, hic⟩ := hIC d (A w)
  set P := holGermIdeal w p with hPdef
  have : P.IsPrime := hPr
  let R := ↥(holGerms (A w))
  let B := ↥(holGerms w) ⧸ P
  have : IsDomain R := hdom
  have : IsIntegrallyClosed R := hic
  let _ : Algebra R B := ((Ideal.Quotient.mk P).comp (pull A w)).toAlgebra

  let cl : anFun w →+* B := (Ideal.Quotient.mk P).comp (toGerm w)
  have hcl0 : ∀ u : anFun w, cl u = 0 ↔ IsGermCombination w p u.1 := fun u => by
    show Ideal.Quotient.mk P (toGerm w u) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact toGerm_mem_iff hp u
  have hcompA : ∀ v : anFun (A w), cl (compA A w v) = algebraMap R B (toGerm (A w) v) := fun v => by
    show Ideal.Quotient.mk P (toGerm w (compA A w v)) = Ideal.Quotient.mk P (pull A w (toGerm (A w) v))
    rw [pull_toGerm]
  have hcomp : ∀ r : R, cl (compA A w (rep r)) = algebraMap R B r := fun r => by
    rw [hcompA, toGerm_rep]

  have hRB : Function.Injective (algebraMap R B) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    rw [← hcomp, hcl0] at hr
    have hev := hinj (rep r).1 (rep r).2 hr
    rw [← toGerm_rep r]
    apply Subtype.ext
    change (((rep r).1 : (Fin d → ℂ) → ℂ) : Germ (𝓝 (A w)) ℂ) = ((0 : (Fin d → ℂ) → ℂ) : Germ _ ℂ)
    exact Germ.coe_eq.2 hev

  let cst : ℂ →+* anFun (A w) :=
    { toFun := fun c => mkA (fun _ => c) analyticAt_const
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ι : ℂ →+* R := (toGerm (A w)).comp cst
  let e := Fintype.equivFin σ
  let crd : σ → anFun w := fun i =>
    mkA (fun z => z i) ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)
  let x : Fin (Fintype.card σ) → B := fun j => cl (crd (e.symm j))

  have hx : Algebra.adjoin R (Set.range x) = ⊤ := by
    rw [eq_top_iff]
    rintro b -
    obtain ⟨ψ, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨u, rfl⟩ := toGerm_surjective w ψ
    obtain ⟨s, a, ha, hc⟩ := hgen u.1 u.2
    let a' : (σ → ℕ) → anFun (A w) := fun m => if hm : m ∈ s then mkA (a m) (ha m hm) else 0
    have hU : ((u - ∑ m ∈ s, compA A w (a' m) * ∏ i, crd i ^ m i : anFun w) : (σ → ℂ) → ℂ) =
        fun z => u.1 z - ∑ m ∈ s, a m (A z) * ∏ i, z i ^ m i := by
      funext z
      simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
        SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, Pi.sub_apply, Finset.sum_apply, Pi.mul_apply,
        Finset.prod_apply, Pi.pow_apply]
      congr 1
      refine Finset.sum_congr rfl fun m hm => ?_
      simp [a', hm, compA, mkA, crd]
    have h0 := (hcl0 _).2 (by rw [hU]; exact hc)
    rw [map_sub, sub_eq_zero, map_sum] at h0
    show cl u ∈ _
    rw [h0]
    refine Subalgebra.sum_mem _ fun m _ => ?_
    rw [map_mul, hcompA, map_prod]
    refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.prod_mem _ fun i _ => ?_)
    rw [map_pow]
    have hmem : cl (crd i) ∈ Set.range x := ⟨e i, by simp [x]⟩
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin hmem) _

  have hxint : ∀ i : σ, IsIntegral R (cl (crd i)) := by
    intro i
    obtain ⟨n', b, hb, hc⟩ := hint i
    refine ⟨X ^ n' + ∑ j : Fin n', C (toGerm (A w) (mkA (b j) (hb j))) * X ^ (j : ℕ),
      monic_X_pow_add (degree_sum_fin_lt _), ?_⟩
    have hV : ((crd i ^ n' + ∑ j : Fin n', compA A w (mkA (b j) (hb j)) * crd i ^ (j : ℕ) : anFun w) :
        (σ → ℂ) → ℂ) = fun z => z i ^ n' + ∑ j, b j (A z) * z i ^ (j : ℕ) := by
      funext z
      simp [compA, mkA, crd, Finset.sum_apply]
    have h0 := (hcl0 _).2 (by rw [hV]; exact hc)
    rw [map_add, map_pow, map_sum] at h0
    simp only [map_mul, map_pow, hcompA] at h0
    rw [eval₂_add, eval₂_X_pow, eval₂_finsetSum]
    simpa [eval₂_mul, eval₂_C, eval₂_X_pow] using h0
  have : Module.Finite R B := by
    refine ⟨?_⟩
    rw [← Algebra.top_toSubmodule, ← hx]
    exact fg_adjoin_of_finite (Set.finite_range x) (by rintro _ ⟨j, rfl⟩; exact hxint _)

  obtain ⟨c, m, D, Q, hmon, -, hdiv, hD0, ⟨a, b, hab⟩, hQ⟩ :=
    GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm.exists_primitive_data hRB ι x hx
  let ℓ : (σ → ℂ) →L[ℂ] ℂ :=
    ∑ j : Fin (Fintype.card σ), c j • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm j)
  let lA : anFun w := mkA ℓ (ℓ.analyticAt w)
  set ℓB : B := ∑ j, algebraMap R B (ι (c j)) * x j with hℓB
  have hlA : cl lA = ℓB := by
    have : lA = ∑ j : Fin (Fintype.card σ), compA A w (cst (c j)) * crd (e.symm j) := by
      apply Subtype.ext
      funext z
      simp [lA, mkA, ℓ, compA, cst, crd, Finset.sum_apply]
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hcompA]
    rfl
  have haev : ∀ (q : R[X]) (K : ℕ), q.natDegree < K →
      aeval ℓB q = cl (∑ j : Fin K, compA A w (rep (q.coeff j)) * lA ^ (j : ℕ)) := by
    intro q K hq
    rw [aeval_eq_sum_range' hq, ← Fin.sum_univ_eq_sum_range (fun i => q.coeff i • ℓB ^ i) K, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hlA, hcomp, Algebra.smul_def]
  set N := m.natDegree with hN
  have hm0 : aeval ℓB m = 0 := (hdiv m).2 dvd_rfl
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp at hm0
  let cf : Fin N → (Fin d → ℂ) → ℂ := fun j => (rep (m.coeff j)).1
  let δ : (Fin d → ℂ) → ℂ := (rep D).1
  refine ⟨d, A, ℓ, N, cf, δ, ⟨fun j => (rep (m.coeff j)).2, (rep D).2, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    have hU : ((lA ^ N + ∑ j : Fin N, compA A w (rep (m.coeff j)) * lA ^ (j : ℕ) : anFun w) :
        (σ → ℂ) → ℂ) = fun z => ℓ z ^ N + ∑ j, cf j (A z) * ℓ z ^ (j : ℕ) := by
      funext z
      simp [lA, mkA, compA, cf, Finset.sum_apply]
    have hcm : cl (lA ^ N + ∑ j : Fin N, compA A w (rep (m.coeff j)) * lA ^ (j : ℕ)) = aeval ℓB m := by
      conv_rhs => rw [hmon.as_sum]
      rw [map_add, map_pow, hlA, map_sum, map_add, map_pow, aeval_X, map_sum,
        ← Fin.sum_univ_eq_sum_range (fun i => aeval ℓB (C (m.coeff i) * X ^ i)) N]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow, hlA, hcomp, map_mul, aeval_C, map_pow, aeval_X]
    have h := (hcl0 _).1 (hcm.trans hm0)
    rw [hU] at h
    exact h
  ·
    intro a' ha' hc' j
    let q : R[X] := ∑ i : Fin N, C (toGerm (A w) (mkA (a' i) (ha' i))) * X ^ (i : ℕ)
    have hq : aeval ℓB q = 0 := by
      have hU : ((∑ i : Fin N, compA A w (mkA (a' i) (ha' i)) * lA ^ (i : ℕ) : anFun w) : (σ → ℂ) → ℂ) =
          fun z => ∑ i, a' i (A z) * ℓ z ^ (i : ℕ) := by
        funext z
        simp [lA, mkA, compA, Finset.sum_apply]
      have h := (hcl0 _).2 (by rw [hU]; exact hc')
      rw [← h, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, aeval_C, aeval_X, map_mul, map_pow, hlA, hcompA]
    have hq0 : q = 0 := by
      refine eq_zero_of_dvd_of_degree_lt ((hdiv q).1 hq) ?_
      rw [degree_eq_natDegree hmon.ne_zero]
      exact degree_sum_fin_lt _
    have hcoef : q.coeff j = toGerm (A w) (mkA (a' j) (ha' j)) := by
      simp only [q, finsetSum_coeff, coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single j (fun i _ hij => if_neg (fun h => hij (Fin.ext h.symm))) (by simp)]
      simp
    rw [hq0, coeff_zero] at hcoef
    have h' := congrArg Subtype.val hcoef.symm
    change ((a' j : (Fin d → ℂ) → ℂ) : Germ (𝓝 (A w)) ℂ) = ((0 : (Fin d → ℂ) → ℂ) : Germ _ ℂ) at h'
    exact Germ.coe_eq.1 h'
  ·
    let G : ((Fin d → ℂ) → ℂ) →+* Germ (𝓝 (A w)) ℂ := Germ.coeRingHom _
    let ιR : R →+* Germ (𝓝 (A w)) ℂ := (holGerms (A w)).subtype
    let lift : R[X] → ((Fin d → ℂ) → ℂ)[X] := fun q =>
      ∑ i ∈ Finset.range (q.natDegree + 1), C (rep (q.coeff i)).1 * X ^ i
    have hGrep : ∀ r : R, G (rep r).1 = ιR r := fun r => congrArg Subtype.val (toGerm_rep r)
    have hlc : ∀ (q : R[X]) (i : ℕ), G ((lift q).coeff i) = ιR (q.coeff i) := by
      intro q i
      simp only [lift, finsetSum_coeff, coeff_C_mul_X_pow]
      by_cases hi : i < q.natDegree + 1
      · rw [Finset.sum_eq_single i (fun j _ hji => if_neg (Ne.symm hji))
          (fun h => absurd (Finset.mem_range.2 hi) h), if_pos rfl, hGrep]
      · rw [Finset.sum_eq_zero (fun j hj => if_neg (fun h => by subst h; exact hi (Finset.mem_range.1 hj))),
          map_zero, coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
    have hlift : ∀ q : R[X], (lift q).map G = q.map ιR := fun q => by
      ext i
      rw [coeff_map, coeff_map, hlc]
    let Fm : ((Fin d → ℂ) → ℂ)[X] := X ^ N + ∑ j : Fin N, C (cf j) * X ^ (j : ℕ)
    have hFm : Fm.map G = m.map ιR := by
      conv_rhs => rw [hmon.as_sum]
      simp only [Fm, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum, Polynomial.map_mul,
        map_C, cf, hGrep]
      rw [← Fin.sum_univ_eq_sum_range (fun i => C (ιR (m.coeff i)) * X ^ i) N]
    let E : ((Fin d → ℂ) → ℂ)[X] := lift a * Fm + lift b * derivative Fm - C δ
    have hE : E.map G = 0 := by
      have h1 : E.map G = (a * m + b * derivative m - C D).map ιR := by
        simp only [E, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, ← derivative_map, hlift, hFm,
          map_C, δ, hGrep]
      rw [h1, hab, sub_self, Polynomial.map_zero]
    have hev : ∀ᶠ y in 𝓝 (A w), ∀ i ∈ E.support, E.coeff i y = 0 := by
      rw [Filter.eventually_all_finset]
      intro i _
      have h := congrArg (fun q => q.coeff i) hE
      simp only [coeff_map, coeff_zero] at h
      exact Germ.coe_eq.1 h
    filter_upwards [hev] with y hy hδy
    let ev : ((Fin d → ℂ) → ℂ) →+* ℂ := Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y
    have hE0 : E.map ev = 0 := by
      ext i
      rw [coeff_map, coeff_zero]
      by_cases hi : E.coeff i = 0
      · rw [hi, map_zero]
      · exact hy i (mem_support_iff.2 hi)
    have hFy : Fm.map ev = monicOfCoeffs fun j => cf j y := by
      simp [Fm, monicOfCoeffs, Polynomial.map_sum, ev]
    rw [separable_def, ← hFy]
    simp only [E, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, map_C, ← derivative_map,
      sub_eq_zero] at hE0
    refine ⟨C (δ y)⁻¹ * (lift a).map ev, C (δ y)⁻¹ * (lift b).map ev, ?_⟩
    rw [mul_assoc, mul_assoc, ← mul_add, hE0, ← C_mul, show ev δ = δ y from rfl, inv_mul_cancel₀ hδy, C_1]
  ·
    intro g hg
    have hall : ∀ z ∈ Algebra.adjoin R (Set.range x),
        ∃ M : ℕ, algebraMap R B D ^ M * z ∈ Algebra.adjoin R {ℓB} := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        exact ⟨1, by rw [pow_one, hQ j]; exact aeval_mem_adjoin_singleton R ℓB⟩
      | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
      | add u v _ _ hu hv =>
        obtain ⟨M₁, h₁⟩ := hu
        obtain ⟨M₂, h₂⟩ := hv
        refine ⟨M₁ + M₂, ?_⟩
        have : algebraMap R B D ^ (M₁ + M₂) * (u + v) = algebraMap R B D ^ M₂ * (algebraMap R B D ^ M₁ * u) +
            algebraMap R B D ^ M₁ * (algebraMap R B D ^ M₂ * v) := by ring
        rw [this]
        exact Subalgebra.add_mem _
          (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ D) _) h₁)
          (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ D) _) h₂)
      | mul u v _ _ hu hv =>
        obtain ⟨M₁, h₁⟩ := hu
        obtain ⟨M₂, h₂⟩ := hv
        refine ⟨M₁ + M₂, ?_⟩
        rw [show algebraMap R B D ^ (M₁ + M₂) * (u * v) =
          (algebraMap R B D ^ M₁ * u) * (algebraMap R B D ^ M₂ * v) by ring]
        exact Subalgebra.mul_mem _ h₁ h₂
    obtain ⟨M, hM⟩ := hall (cl (mkA g hg)) (by rw [hx]; exact Algebra.mem_top)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hM
    obtain ⟨Q', hQ'⟩ := hM
    have hr : aeval ℓB (Q' %ₘ m) = algebraMap R B D ^ M * cl (mkA g hg) := by
      rw [aeval_modByMonic_eq_self_of_root hm0]
      exact hQ'
    have hrdeg : (Q' %ₘ m).natDegree < N := natDegree_modByMonic_lt Q' hmon hm1
    refine ⟨M, fun j => (rep ((Q' %ₘ m).coeff j)).1, fun j => (rep ((Q' %ₘ m).coeff j)).2, ?_⟩
    have hU : ((compA A w (rep D) ^ M * mkA g hg -
        ∑ j : Fin N, compA A w (rep ((Q' %ₘ m).coeff j)) * lA ^ (j : ℕ) : anFun w) : (σ → ℂ) → ℂ) =
        fun z => δ (A z) ^ M * g z - ∑ j : Fin N, (rep ((Q' %ₘ m).coeff j)).1 (A z) * ℓ z ^ (j : ℕ) := by
      funext z
      simp [lA, mkA, compA, δ, Finset.sum_apply]
    rw [← hU, ← hcl0, map_sub, ← haev _ N hrdeg, hr, map_mul, map_pow, hcomp, sub_self]
  ·
    intro g hg
    exact hCE σ w k p d A hp hint hgen g hg
  ·
    intro hδ
    have h0 : cl (compA A w (rep D)) = 0 := (hcl0 _).2 hδ
    rw [hcomp] at h0
    exact hD0 (hRB (h0.trans (map_zero _).symm))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermPrimitivePresentation
