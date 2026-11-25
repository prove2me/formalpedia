-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_dualSub_fg_6e089a7ed252
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:41.174529+00:00
-- url     : https://prove2.me/submissions/323e28dd-a41f-4e90-8bb8-bf715a015bb9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExist

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω] {τ : Type*}
  {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace TwistedDualGensExist
theorem _root_.solution [IsNoetherianRing O] [Fintype τ] {x : τ → Ω}
    (B : ChartBundle O x r E) {c : τ} (hc : x c ≠ 0) :
    (TwistedDualGensExist.dualSub B c).FG := by
  have : IsNoetherianRing (chartRing O x c) :=
    isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  obtain ⟨k, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b hli hsp hiff using hb
  obtain ⟨l0, hl0⟩ : ∃ l0, f l0 ≠ 0 := by
    by_contra! h
    simp [h] at hsum
  set β : Module.Basis (Fin r) Ω E := Module.Basis.mk (hli l0) (hsp l0).ge with hβdef
  have hβ : ∀ q, β q = b l0 q := fun q => Module.Basis.mk_apply _ _ _
  have hbl : ∀ q, ∃ n : ℕ, f l0 ^ n • β q ∈ B.lat c := fun q => by
    rw [hβ]
    exact (hiff l0 (b l0 q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by by_cases h : q' = q <;> simp [h]⟩,
      by simp [Pi.single_apply]⟩
  choose n hn using hbl
  set N := ∑ q, n q with hNdef
  have hN : ∀ q, f l0 ^ N • β q ∈ B.lat c := by
    intro q
    have hq : n q ≤ N := Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have : f l0 ^ N • β q = f l0 ^ (N - n q) • (f l0 ^ n q • β q) := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hq]
    rw [this]
    exact B.stable c _ (pow_mem (hf l0) _) _ (hn q)
  have hf0 : f l0 ^ N ≠ 0 := pow_ne_zero _ hl0
  refine Submodule.FG.of_le (Submodule.fg_span (Set.finite_range fun q => (f l0 ^ N)⁻¹ • β.coord q)) ?_
  intro ψ hψ
  have hψ' : ∀ v ∈ B.lat c, ψ v ∈ chartRing O x c := hψ
  rw [← β.sum_dual_apply_smul_coord ψ]
  refine Submodule.sum_mem _ fun q _ => ?_
  have hmem : f l0 ^ N * ψ (β q) ∈ chartRing O x c := by
    have := hψ' _ (hN q)
    rwa [map_smul, smul_eq_mul] at this
  have : ψ (β q) • β.coord q = (⟨_, hmem⟩ : chartRing O x c) • ((f l0 ^ N)⁻¹ • β.coord q) := by
    show _ = (f l0 ^ N * ψ (β q)) • ((f l0 ^ N)⁻¹ • β.coord q)
    rw [smul_smul]
    congr 1
    field_simp
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
end TwistedDualGensExist
end GroundTheory.Heights₂.Heights.NumbersDVR
