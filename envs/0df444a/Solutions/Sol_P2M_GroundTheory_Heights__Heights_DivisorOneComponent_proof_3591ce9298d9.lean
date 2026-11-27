-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DivisorOneComponent_proof_3591ce9298d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:55:54.208539+00:00
-- url     : https://prove2.me/submissions/10e008e2-ca4e-44fd-9a9d-1afc16fd723e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorOneComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMultGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorOneComponent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivisorOneComponent_mem_zeroSet_iff_5aca8d1e7795
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivisorOneComponent_isClosed_zeroSet_e95e7da77948
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivisorOneComponent_exists_bound_cfb01f74d8c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivisorOneComponent_dim_sup_add_one_le_ada06419a714
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_inf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_quotient_dim_le_of_minimalPrimes_b2ad850cbdc7


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
open MvPolynomial Filter Topology ComplexSets
noncomputable section
open DivisorOneComponent
namespace GroundTheory.Heights₂.Heights
namespace DivisorOneComponent
theorem _root_.solution : DivisorOneComponent.Statement := by
  classical
  intro n d J u hJ hdim hu
  have hKq : ∀ x ∈ zeroSet J, linEval u x = 0 → J ⊔ Ideal.span {linForm u} ≤ RingHom.ker (eval x) := by
    intro x hxJ hxu
    refine sup_le ((mem_zeroSet_iff J x).1 hxJ) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    simpa [linForm, linEval] using hxu
  generalize hK : J ⊔ Ideal.span {linForm u} = K at hKq ⊢
  have hM : K.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  obtain ⟨S, hS⟩ : ∃ S : Finset (Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ)),
      ∀ p, p ∈ S ↔ p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2 :=
    ⟨(hM.prod hM).toFinset.filter fun p => p.1 ≠ p.2, fun p => by rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_prod, and_assoc]⟩
  obtain ⟨I, hI⟩ : ∃ I, I = S.inf fun p => p.1 ⊔ p.2 := ⟨_, rfl⟩
  have hmemS : ∀ p ∈ S, p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2 := fun p hp => (hS p).1 hp
  have hpair : ∀ W W', W ∈ K.minimalPrimes → W' ∈ K.minimalPrimes → W ≠ W' → I ≤ W ⊔ W' :=
    fun W W' hW hW' hne => by
      have h := Finset.inf_le (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ((hS (W, W')).2 ⟨hW, hW', hne⟩)
      rw [hI]; exact h
  have hKI : K ≤ I := by
    have h := Finset.le_inf (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) (a := K) (s := S) fun p hp => (hmemS p hp).1.1.2.trans le_sup_left
    rw [hI]; exact h
  obtain ⟨N, hN, hxN⟩ := exists_bound d
  refine ⟨I, hKI, ?_, ?_⟩
  · refine lt_of_le_of_lt (ComplexSets.quotient_dim_le_of_minimalPrimes I fun Z hZ => ?_) hN
    have hZI : S.inf (fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ≤ Z := by rw [← hI]; exact hZ.1.2
    obtain ⟨p, hp, hpZ⟩ := (Ideal.IsPrime.inf_le' (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) hZ.1.1).1 hZI
    obtain ⟨h1, h2, h12⟩ := hmemS p hp
    exact (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hpZ)).trans
      (hxN _ (dim_sup_add_one_le hu hdim (by rw [hK]; exact h1) (by rw [hK]; exact h2) h12))
  · intro q hqJ hqu hqI
    obtain ⟨W, hW, hWq⟩ := Ideal.exists_minimalPrimes_le (hKq q hqJ hqu)
    have huniq : ∀ W' ∈ K.minimalPrimes, q ∈ zeroSet W' → W' = W := by
      intro W' hW' hq'
      by_contra hne
      exact hqI ((mem_zeroSet_iff I q).2 ((hpair W W' hW hW' (Ne.symm hne)).trans
        (sup_le hWq ((mem_zeroSet_iff W' q).1 hq'))))
    refine ⟨W, hW, (mem_zeroSet_iff W q).2 hWq, huniq, ⋂ W' ∈ K.minimalPrimes \ {W}, (zeroSet W')ᶜ, ?_, ?_⟩
    · refine (biInter_mem (hM.subset Set.sdiff_subset)).2 fun W' hW' => (isClosed_zeroSet W').isOpen_compl.mem_nhds ?_
      exact fun hq' => hW'.2 (huniq W' hW'.1 hq')
    · rintro x ⟨hxJ, hxU⟩ hxu
      obtain ⟨W'', hW'', hW''x⟩ := Ideal.exists_minimalPrimes_le (hKq x hxJ hxu)
      by_cases h : W'' = W
      · subst h; exact (mem_zeroSet_iff W'' x).2 hW''x
      · exact absurd ((mem_zeroSet_iff W'' x).2 hW''x) (Set.mem_iInter₂.1 hxU W'' ⟨hW'', h⟩)
end DivisorOneComponent
end GroundTheory.Heights₂.Heights
