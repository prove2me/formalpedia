-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence.exists_beta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:57.7545+00:00
-- url     : https://prove2.me/submissions/d79863ac-96e9-4762-bbdd-ea67628ae51f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalComplementLines
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
theorem _root_.solution (X : Data E r) {ξ : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0) :
    ∃ β : Fin (r - 2) → Fin r → E, (∀ k, herm X.Gm (β k) ξ = 0) ∧
      LinearIndependent E (Fin.cons ξ β : Fin (r - 2 + 1) → Fin r → E) ∧
      (∀ x : Fin r → E, herm X.Gm x ξ = 0 →
        ∃ (c : Fin (r - 2) → E) (e : E), x = ∑ k, c k • β k + e • ξ) := by
  classical
  set f := hxi X.Gm ξ with hf
  have hfx : ∀ x, f x = herm X.Gm x ξ := fun _ => rfl

  have hw : (fun b => cc (ξ b)) ≠ 0 := by
    intro h
    apply hξ0
    funext b
    have hb := congrFun h b
    simp only [Pi.zero_apply, cc] at hb
    simpa using hb
  obtain ⟨a, ha⟩ : ∃ a, (X.Gm *ᵥ fun b => cc (ξ b)) a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det (funext h))
  have hfa : f (Pi.single a 1) ≠ 0 := by
    rw [hfx]
    convert ha using 1
    simp [herm, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hsurj : Function.Surjective f := fun y =>
    ⟨(y / f (Pi.single a 1)) • Pi.single a 1, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfa]⟩
  set K := LinearMap.ker f with hK
  have hξK : ξ ∈ K := by rw [LinearMap.mem_ker, hfx]; exact hξξ
  have hrange : Module.finrank E (LinearMap.range f) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hKr : Module.finrank E K = r - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, Module.finrank_fin_fun] at this
    have h2 : 1 + Module.finrank E K = r := this
    omega
  have hKpos : 0 < Module.finrank E K := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro h
    apply hξ0
    have : ξ ∈ (⊥ : Submodule E (Fin r → E)) := h ▸ hξK
    simpa using this
  have hr2 : 2 ≤ r := by omega
  set ξK : K := ⟨ξ, hξK⟩ with hξKdef
  have hξK0 : ξK ≠ 0 := fun h => hξ0 (congrArg Subtype.val h)
  set S : Submodule E K := E ∙ ξK with hS
  have hQ : Module.finrank E (K ⧸ S) = r - 2 := by
    have h0 := Submodule.finrank_quotient_add_finrank S
    have h1 : Module.finrank E S = 1 := by rw [hS]; exact finrank_span_singleton hξK0
    rw [h1, hKr] at h0
    have h2 : Module.finrank E (K ⧸ S) + 1 = r - 1 := h0
    omega
  let bQ := Module.finBasisOfFinrankEq E (K ⧸ S) hQ
  let βK : Fin (r - 2) → K := fun k => (Submodule.Quotient.mk_surjective S (bQ k)).choose
  have hβK : ∀ k, Submodule.Quotient.mk (p := S) (βK k) = bQ k := fun k =>
    (Submodule.Quotient.mk_surjective S (bQ k)).choose_spec
  have hdecK : ∀ y : K, ∃ (c : Fin (r - 2) → E) (e : E), y = ∑ k, c k • βK k + e • ξK := by
    intro y
    set c := bQ.repr (Submodule.Quotient.mk y) with hc
    refine ⟨c, ?_⟩
    have hmk : Submodule.Quotient.mk (p := S) (∑ k, c k • βK k) = ∑ k, c k • bQ k := by
      have h := map_sum S.mkQ (fun k => c k • βK k) Finset.univ
      simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, hβK] at h
      exact h
    have hq : Submodule.Quotient.mk (p := S) y = Submodule.Quotient.mk (∑ k, c k • βK k) := by
      rw [hmk, hc, bQ.sum_repr]
    rw [Submodule.Quotient.eq] at hq
    have hq' : y - ∑ k, c k • βK k ∈ E ∙ ξK := hq
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hq'
    exact ⟨e, by rw [he]; abel⟩
  refine ⟨fun k => (βK k : Fin r → E), fun k => (βK k).2, ?_, ?_⟩
  · have hspan : ⊤ ≤ Submodule.span E (Set.range (Fin.cons ξK βK : Fin (r - 2 + 1) → K)) := by
      intro y _
      obtain ⟨c, e, rfl⟩ := hdecK y
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_)
        (Submodule.smul_mem _ _ ?_)
      · exact Submodule.subset_span ⟨k.succ, by simp⟩
      · exact Submodule.subset_span ⟨0, by simp⟩
    have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspan
      (by rw [Fintype.card_fin, hKr]; omega)
    have hmap := hli.map' K.subtype (Submodule.ker_subtype K)
    have heq : (K.subtype ∘ (Fin.cons ξK βK : Fin (r - 2 + 1) → K)) =
        (Fin.cons ξ (fun k => (βK k : Fin r → E)) : Fin (r - 2 + 1) → Fin r → E) := by
      funext i
      refine Fin.cases ?_ (fun k => ?_) i <;> simp [ξK]
    exact heq ▸ hmap
  · intro x hx
    have hxK : x ∈ K := by rw [LinearMap.mem_ker, hfx]; exact hx
    obtain ⟨c, e, he⟩ := hdecK ⟨x, hxK⟩
    refine ⟨c, e, ?_⟩
    have := congrArg Subtype.val he
    simpa [ξK] using this
end ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
