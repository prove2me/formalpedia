-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_exists_ext_b6f487c55f36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:04:31.38712+00:00
-- url     : https://prove2.me/submissions/bde390db-6e55-4903-84b1-b73a4ee8b5c7

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_norm_le_pow_1bb8f3f89542
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_denseRange_emb_e16ca7438e57


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω]
variable [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l)
variable {j} {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
include hj
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (g : G E Ω) (hg : g ∈ Dec (F := E) A) :
    ∃ σ : GQ l, ∀ x, σ (j x) = j (g x) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  let iC : Ω →+* ℂ_[l] := (algebraMap (PadicAlgCl l) ℂ_[l]).comp j
  letI : PseudoMetricSpace Ω := PseudoMetricSpace.induced iC inferInstance
  have ue : IsUniformInducing iC := ⟨rfl⟩
  have dr : DenseRange iC :=
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).comp (denseRange_emb l j)
      (UniformSpace.Completion.continuous_coe _)
  let f : Ω →+* ℂ_[l] := iC.comp (g : Ω →+* Ω)
  have hn : ∀ z : Ω, ‖iC z‖ = ‖j z‖ := fun z => PadicComplex.norm_extends l (j z)
  have hl1 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    have h1 : ‖((l : ℕ) : PadicAlgCl l)‖ = ‖((l : ℕ) : ℚ_[l])‖ := by
      rw [← PadicAlgCl.norm_extends, map_natCast]
    rw [h1]
    exact Padic.norm_p_lt_one
  have hf : UniformContinuous f := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one hε hl1
    refine ⟨‖((l : ℕ) : PadicAlgCl l)‖ ^ n,
      pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)) n, fun {a b} hab => ?_⟩
    have h1 : dist a b = ‖j (a - b)‖ := by
      show dist (iC a) (iC b) = _
      rw [dist_eq_norm, ← map_sub, hn]
    have h2 : dist (f a) (f b) = ‖j (g (a - b))‖ := by
      rw [dist_eq_norm, ← map_sub]
      exact hn _
    rw [h2]
    rw [h1] at hab
    exact lt_of_le_of_lt (norm_le_pow hj g hg _ n hab.le) hn'
  let gh : ℂ_[l] →+* ℂ_[l] := IsDenseInducing.extendRingHom ue dr hf
  have hgh : ∀ x, gh (iC x) = f x := fun x => (ue.isDenseInducing dr).extend_eq hf.continuous x
  have hcont : Continuous gh := (uniformContinuous_uniformly_extend ue dr hf).continuous
  have hQ : ∀ x : ℚ_[l], gh (algebraMap ℚ_[l] ℂ_[l] x) = algebraMap ℚ_[l] ℂ_[l] x := by
    have hc : Continuous (algebraMap ℚ_[l] ℂ_[l]) := continuous_algebraMap ℚ_[l] ℂ_[l]
    have e := (Padic.denseRange_ratCast l).equalizer (hcont.comp hc) hc (funext fun q => by
      show gh (algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l])) = algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l])
      rw [map_ratCast, map_ratCast])
    exact fun x => congrFun e x
  let gA : ℂ_[l] →ₐ[ℚ_[l]] ℂ_[l] := { gh with commutes' := hQ }
  refine ⟨gA.restrictNormal' (PadicAlgCl l), fun x => ?_⟩
  have h3 := AlgHom.restrictNormal_commutes gA (PadicAlgCl l) (j x)
  exact (algebraMap (PadicAlgCl l) ℂ_[l]).injective (h3.trans (hgh x))
end Formalism.BasicNotions.Examples₂.LB
