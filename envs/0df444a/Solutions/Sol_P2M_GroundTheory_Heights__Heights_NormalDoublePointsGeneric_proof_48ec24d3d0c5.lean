-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_proof_48ec24d3d0c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:04:53.808347+00:00
-- url     : https://prove2.me/submissions/b3b1eba9-e363-4b6f-837c-4b134923b0a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalDoublePointsGeneric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quotient_le_of_primes_0048121322f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quotient_anti_daa7b5be1ca9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quot_sup_span_add_one_le_1de9644a92aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_belowNat_lt_4cbdfa3d72d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_le_belowNat_of_add_two_le_aedb9d1a4179

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
open MvPolynomial Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
namespace GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
theorem _root_.solution : NormalDoublePointsGeneric.Statement := by
  intro n d J u M hJ hdim hu
  classical
  choose a b hbJ hab using M.birational
  set bb : MvPolynomial (Fin n) ℂ := ∏ i, b i with hbb
  have hbbJ : bb ∉ J := fun h => by
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hJ)).1 h
    exact hbJ i hi
  set K : Ideal (MvPolynomial (Fin n) ℂ) := J ⊔ Ideal.span {bb} with hK
  have hfin : K.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  set S : Finset (Ideal (MvPolynomial (Fin n) ℂ)) := hfin.toFinset.filter (fun P => linForm u ∉ P) with hS
  have memS : ∀ P, P ∈ S ↔ P ∈ K.minimalPrimes ∧ linForm u ∉ P := fun P => by
    simp [hS]
  refine ⟨S.inf (fun P => P ⊔ Ideal.span {linForm u}), ?_, ?_, ?_⟩
  · refine Finset.le_inf fun P hP => sup_le_sup_right ?_ _
    exact le_sup_left.trans ((memS P).1 hP).1.1.2
  · have := hJ
    have hdimK : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
      hdim ▸ ringKrullDim_quot_sup_span_add_one_le J hbbJ
    refine lt_of_le_of_lt (ringKrullDim_quotient_le_of_primes _ (belowNat d) fun W hW hIW => ?_) (belowNat_lt d)
    obtain ⟨P, hPS, hPW⟩ := (hW.inf_le').1 hIW
    refine ⟨_, hPW, le_belowNat_of_add_two_le ?_⟩
    obtain ⟨hPm, huP⟩ := (memS P).1 hPS
    have := hPm.1.1
    have h1 := ringKrullDim_quot_sup_span_add_one_le P huP
    have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) :=
      ringKrullDim_quotient_anti hPm.1.2
    calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (P ⊔ Ideal.span {linForm u})) + 1 + 1
        ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) + 1 := by gcongr; exact h1.trans h2
      _ ≤ _ := hdimK
  · intro q _ hqu hqI
    have evu : ∀ x, eval x (linForm u) = linEval u x := fun x => by simp [linForm, linEval]
    have hqP : ∀ P ∈ S, q ∉ zeroSet P := by
      intro P hP hqP
      apply hqI
      intro f hf
      have hf' : f ∈ P ⊔ Ideal.span {linForm u} := (Finset.inf_le (f := fun P => P ⊔ Ideal.span {linForm u}) hP) hf
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.1 hf'
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      simp [hqP p hp, evu, hqu]
    have hclosed : ∀ P : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet P) := fun P => by
      have : zeroSet P = ⋂ f ∈ P, {x : Fin n → ℂ | eval x f = 0} := by
        ext x; simp [zeroSet]
      rw [this]
      exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const
    refine ⟨⋂ P ∈ S, (zeroSet P)ᶜ, (Filter.biInter_finset_mem S).2 fun P hP =>
      (hclosed P).isOpen_compl.mem_nhds (hqP P hP), ?_⟩
    intro w hw w' hw' hww hxN hne
    set x := IndefiniteRowSideFullHecke.ComplexSets.firstCoords w with hx
    have hwx : (w ∘ Sum.inl) = x := rfl
    have hw'x : (w' ∘ Sum.inl) = x := by rw [hww]; rfl
    have hxJ : ∀ f ∈ J, eval x f = 0 := fun f hf => by
      have hf' : rename Sum.inl f ∈ M.ideal := by
        rw [← M.comap_eq] at hf; exact hf
      have := hw _ hf'
      rwa [eval_rename, hwx] at this
    have hbx : eval x bb = 0 := by
      by_contra hb
      apply hne
      funext s
      rcases s with i | i
      · exact congrFun hww i
      · have hbi : eval x (b i) ≠ 0 := fun h0 => hb (by
          rw [hbb, map_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) h0)
        have e1 := hw _ (hab i)
        have e2 := hw' _ (hab i)
        simp only [map_sub, map_mul, eval_rename, eval_X, hwx, hw'x] at e1 e2
        exact mul_left_cancel₀ hbi (by linear_combination e1 - e2)
    have hKx : K ≤ RingHom.ker (eval x) := sup_le (fun f hf => RingHom.mem_ker.2 (hxJ f hf))
      (Ideal.span_le.2 (Set.singleton_subset_iff.2 (RingHom.mem_ker.2 hbx)))
    have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨P, hPm, hPx⟩ := Ideal.exists_minimalPrimes_le hKx
    by_cases huP : linForm u ∈ P
    · rw [← evu]; exact RingHom.mem_ker.1 (hPx huP)
    · exfalso
      have hPS : P ∈ S := (memS P).2 ⟨hPm, huP⟩
      have hxP : x ∈ zeroSet P := fun f hf => RingHom.mem_ker.1 (hPx hf)
      exact (Set.mem_iInter₂.1 hxN P hPS) hxP
end GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
