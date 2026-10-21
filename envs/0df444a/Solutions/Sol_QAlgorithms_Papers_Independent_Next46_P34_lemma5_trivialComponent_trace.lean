-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P34.lemma5_trivialComponent_trace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:29:46.217317+00:00
-- url     : https://prove2.me/submissions/304e787b-d235-4296-81c3-d64aa7bf3a3f

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P34
noncomputable section
open scoped BigOperators

namespace G62T5

open Module LinearMap

/-- trace of a power on a generalized eigenspace -/
theorem trace_pow_restrict {L V : Type*} [Field L] [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (f : End L V) (μ : L) (i : ℕ) :
    trace L (f.maxGenEigenspace μ) ((f ^ i).restrict (f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right i) μ))
      = μ ^ i * finrank L (f.maxGenEigenspace μ) := by
  set g := f.restrict (f.mapsTo_maxGenEigenspace_of_comm rfl μ) with hg
  have hpow : ∀ j, (f ^ j).restrict (f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ) = g ^ j := by
    have key : ∀ k (y : f.maxGenEigenspace μ), (((g ^ k) y : f.maxGenEigenspace μ) : V) = (f ^ k) y := by
      intro k
      induction k with
      | zero => intro y; simp
      | succ k ih =>
        intro y
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
        rfl
    intro j
    ext x
    rw [key]; rfl
  rw [hpow]
  have hn := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  induction i with
  | zero => simp
  | succ j ih =>
    have hn' : IsNilpotent (g - algebraMap L _ μ) := by
      convert hn using 1
      ext x
      simp [hg]
      rfl
    rw [pow_succ, Module.End.mul_eq_comp, trace_comp_eq_mul_of_commute_of_isNilpotent μ
      ((Commute.refl g).pow_left j) hn', ih]
    ring


theorem trace_pow_roots {L : Type*} [Field L] [IsAlgClosed L] {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) L) (i : ℕ) :
    (Y ^ i).trace = (Y.charpoly.roots.map (· ^ i)).sum := by
  classical
  set f : Module.End L (Fin n → L) := Matrix.toLin' Y with hf
  have h1 : (Y ^ i).trace = trace L _ (f ^ i) := by
    rw [hf, ← Matrix.toLin'_pow, Matrix.trace_toLin'_eq]
  have htop := Module.End.iSup_maxGenEigenspace_eq_top f
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace htop
  have hfin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  rw [h1, LinearMap.trace_eq_sum_trace_restrict' hint hfin
    (fun μ => f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right i) μ)]
  simp_rw [trace_pow_restrict, LinearMap.finrank_maxGenEigenspace_eq, hf, Matrix.charpoly_toLin']
  rw [Finset.sum_multiset_map_count]
  have hz : ∀ μ, μ ∉ hfin.toFinset → (Y.charpoly.rootMultiplicity μ : L) = 0 := by
    intro μ hμ
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hμ
    have := LinearMap.finrank_maxGenEigenspace_eq f μ
    rw [hμ, finrank_bot, hf, Matrix.charpoly_toLin'] at this
    rw [← this]; simp
  have hS : ∑ μ ∈ hfin.toFinset, μ ^ i * (Y.charpoly.rootMultiplicity μ : L) =
      ∑ μ ∈ hfin.toFinset ∪ Y.charpoly.roots.toFinset, μ ^ i * (Y.charpoly.rootMultiplicity μ : L) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro μ _ hμ; rw [hz μ hμ, mul_zero]
  have hT : ∑ μ ∈ Y.charpoly.roots.toFinset, Y.charpoly.roots.count μ • μ ^ i =
      ∑ μ ∈ hfin.toFinset ∪ Y.charpoly.roots.toFinset, Y.charpoly.roots.count μ • μ ^ i := by
    apply Finset.sum_subset Finset.subset_union_right
    intro μ _ hμ
    rw [Multiset.mem_toFinset] at hμ
    rw [Multiset.count_eq_zero_of_notMem hμ, zero_smul]
  rw [hS, hT]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Polynomial.count_roots, nsmul_eq_mul, mul_comm]

end G62T5

open QAlgorithms.Papers.Independent.Next46.P34

namespace G62T5

theorem moments {F K : Type*} [Field F] [Field K] [Algebra F K] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) F) (alpha : Fin n → K)
    (hroots : X.charpoly.map (algebraMap F K) = ∏ k, (Polynomial.X - Polynomial.C (alpha k)))
    (i : ℕ) : ∑ k, alpha k ^ i = algebraMap F K (Matrix.trace (X ^ i)) := by
  set ι := algebraMap K (AlgebraicClosure K)
  apply ι.injective
  set φ : F →+* AlgebraicClosure K := ι.comp (algebraMap F K)
  have hY : (X.map φ).charpoly = ∏ k, (Polynomial.X - Polynomial.C (ι (alpha k))) := by
    rw [Matrix.charpoly_map, show φ = ι.comp (algebraMap F K) from rfl, ← Polynomial.map_map, hroots,
      Polynomial.map_prod]
    simp
  have hroots' : (X.map φ).charpoly.roots = Finset.univ.val.map (fun k => ι (alpha k)) := by
    rw [hY, Finset.prod_eq_multiset_prod]
    have e : Multiset.map (fun k => Polynomial.X - Polynomial.C (ι (alpha k))) Finset.univ.val =
        (Finset.univ.val.map (fun k => ι (alpha k))).map (fun a => Polynomial.X - Polynomial.C a) := by
      rw [Multiset.map_map]; rfl
    rw [e, Polynomial.roots_multiset_prod_X_sub_C]
  have htr := trace_pow_roots (X.map φ) i
  have htm : ((X ^ i).map φ).trace = φ (X ^ i).trace := by
    simp [Matrix.trace, map_sum]
  rw [hroots', Multiset.map_map, ← Matrix.map_pow, htm] at htr
  rw [map_sum]
  simp only [map_pow]
  rw [show ι (algebraMap F K (X ^ i).trace) = φ (X ^ i).trace from rfl, htr]
  rfl

end G62T5

theorem solution
    {F K : Type*} [Field F] [CharZero F] [Field K] [CharZero K]
    [Algebra F K] [FiniteDimensional F K]
    {n : ℕ} (hn : 0 < n) (X : Matrix (Fin n) (Fin n) F)
    (hsemisimple : Module.End.IsSemisimple (Matrix.toLin' X))
    [Polynomial.IsSplittingField F K X.charpoly]
    (alpha : Fin n → K)
    (hroots : X.charpoly.map (algebraMap F K) =
      ∏ k, (Polynomial.X - Polynomial.C (alpha k)))
    (action : (K ≃ₐ[F] K) →* Equiv.Perm (Fin n))
    (hrootAction : ∀ (sigma : K ≃ₐ[F] K) k, sigma (alpha k) = alpha (action sigma k)) :
    (trivialComponent n ≤ rationalRelations alpha ↔ X.charpoly.coeff (n - 1) = 0) ∧
      ∀ i : ℕ, rootPowerMoment alpha i (fun _ => 1) = algebraMap F K (Matrix.trace (X ^ i)) := by
  have hm := G62T5.moments X alpha hroots
  have hrpm : ∀ i, rootPowerMoment alpha i (fun _ => 1) = ∑ k, alpha k ^ i := by
    intro i; simp [rootPowerMoment]
  refine ⟨?_, fun i => by rw [hrpm, hm]⟩
  rw [trivialComponent, Submodule.span_singleton_le_iff_mem, rationalRelations, LinearMap.mem_ker]
  have hrf : rootFunctional alpha (fun _ => (1 : ℚ)) = ∑ k, alpha k := by
    simp [rootFunctional]
  rw [hrf]
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h1 := hm 1
  simp only [pow_one] at h1
  rw [h1, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, map_neg, neg_eq_zero,
    (algebraMap F K).injective.eq_iff' (map_zero _)]
