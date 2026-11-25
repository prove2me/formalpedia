-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_proof_217df29a6fd6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:23:31.718853+00:00
-- url     : https://prove2.me/submissions/01750e81-84c5-47a9-92f4-4b549652ca24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHilbDegBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_isMultiHomogIdeal_sup_span_b40aa895ecac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_lt_of_add_one_le_natCast_8307ccbc963c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_le_natCast_of_lt_natCast_succ_e06a86729995
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_degLT_listSum_94fc907d46a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_degLT_zero_8822dfd84ef9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open HilbDegBound
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace HilbDegBound
theorem _root_.solution (h1 : HilbFnVanishBlock.Statement.{u}) (h2 : HilbFnCut.Statement.{u})
    (h3 : PrimeFiltration.Statement.{u}) (h4 : DimStrictDrop.Statement.{u})
    (h5 : RelevantDimGe.Statement.{u}) (h6 : DegLTClosure.Statement)
    (h7 : DegLTOfUnitSteps.Statement) : HilbDegBound.Statement.{u} := by
  intro F _ K _ _ ι _ n

  have irr : ∀ (n : ℕ) (Q : Ideal (MRing ι F)), ¬ IsRelevant Q → DegLT (hilbFn Q) n := by
    intro n Q hrel
    unfold IsRelevant at hrel
    push Not at hrel
    obtain ⟨k, hk⟩ := hrel
    have hev : (0 : (K → ℤ) → ℤ) =ᶠ[Filter.atTop] hilbFn Q := by
      filter_upwards [Filter.eventually_ge_atTop (1 : K → ℤ)] with m hm
      exact (h1 F K ι Q k hk m (hm k)).symm
    exact (h6 K n 0 _ 0 0).2.2.2.2 hev (degLT_zero n)
  induction n with
  | zero =>
    intro Q hQ hQh hdim
    by_cases hrel : IsRelevant Q
    · exfalso
      have hge := h5 F K ι Q ⟨hQ, hQh, hrel⟩
      rw [Nat.zero_add] at hdim
      exact absurd hge (not_le.mpr hdim)
    · exact irr 0 Q hrel
  | succ n ih =>
    intro Q hQ hQh hdim
    by_cases hrel : IsRelevant Q
    swap
    · exact irr _ Q hrel
    have hdimle : ringKrullDim (MRing ι F ⧸ Q) ≤ ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      have e : n + 1 + Fintype.card K = n + Fintype.card K + 1 := by omega
      rw [e] at hdim
      exact le_natCast_of_lt_natCast_succ hdim
    apply h7 K n
    intro k
    obtain ⟨i, hi⟩ := hrel k
    have hx : IsMultiHomog (X ⟨k, i⟩ : MRing ι F) (Pi.single k 1) := isWeightedHomogeneous_X _ _ _
    have hnzd : ∀ y, (X ⟨k, i⟩ : MRing ι F) * y ∈ Q → y ∈ Q :=
      fun y hy => (hQ.mem_or_mem hy).resolve_left hi
    have hcut := h2 F K ι Q (X ⟨k, i⟩) (Pi.single k 1) hQh hx hnzd
    have hJ : IsMultiHomogIdeal (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) :=
      isMultiHomogIdeal_sup_span hQh hx
    have hs : (fun j => ((Pi.single k 1 : K → ℕ) j : ℤ)) = (Pi.single k 1 : K → ℤ) := by
      funext j
      by_cases h : j = k <;> simp [h]
    have heq : diffStep (Pi.single k 1) (hilbFn Q) =
        hilbFn (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) := by
      funext m
      rw [hcut m, hs]
      rfl
    rw [heq]
    obtain ⟨l, hl1, hl2, -⟩ := h3 F K ι _ hJ
    obtain ⟨G, hG⟩ : ∃ G : Ideal (MRing ι F) × (K → ℕ) → (K → ℤ) → ℤ,
        G = fun p => shiftFn (fun j => (p.2 j : ℤ)) (hilbFn p.1) := ⟨_, rfl⟩
    have hfun : hilbFn (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) = fun m =>
        (l.map fun p => G p m).sum := by
      funext m
      rw [hl2 m, hG]
      rfl
    rw [hfun]
    apply degLT_listSum h6 n G l
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := hl1 p hp
    rw [hG]
    refine (h6 K n (hilbFn p.1) 0 0 _).2.2.1 ?_
    refine ih p.1 hp1 hp2 ?_
    have hlt : Q < p.1 := by
      refine lt_of_le_of_ne (le_sup_left.trans hp3) fun h => hi ?_
      rw [h]
      exact hp3 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have := hQ
    have := hp1
    have hd := h4 (MRing ι F) Q p.1 hlt
    exact lt_of_add_one_le_natCast (hd.trans hdimle)
end HilbDegBound
end GroundTheory.Heights₂.Heights.NumbersDVR
