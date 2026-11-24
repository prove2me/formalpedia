-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qi11.tendsto_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:37.675651+00:00
-- url     : https://prove2.me/submissions/764ff63b-3153-4b9a-8843-cee41add7697

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TendstoCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped Classical
private theorem UpperTheory.Reformulated.B.Qi11.tendsto_cut {ι : Type*} {R : ι → Type*} [∀ i, Zero (R i)]
    [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)} (h0 : ∀ i, (0 : R i) ∈ A i)
    (y z : RestrictedProduct R A Filter.cofinite) (hz : ∀ i, z i = 0)
    (f : Finset ι → RestrictedProduct R A Filter.cofinite)
    (hf : ∀ B i, f B i = if i ∈ B then 0 else y i) :
    Filter.Tendsto f Filter.atTop (nhds z) := by
  have hS : Filter.cofinite ≤ Filter.principal {i | y i ∈ A i} := Filter.le_principal_iff.2 y.2
  let g : Finset ι → RestrictedProduct R A (Filter.principal {i | y i ∈ A i}) := fun B =>
    ⟨fun i => if i ∈ B then 0 else y i, fun i hi => by
      show (if i ∈ B then 0 else y i) ∈ A i
      split_ifs
      · exact h0 i
      · exact hi⟩
  let o : RestrictedProduct R A (Filter.principal {i | y i ∈ A i}) := ⟨fun _ => 0, fun i _ => h0 i⟩
  have hg : Filter.Tendsto g Filter.atTop (nhds o) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro i
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({i} : Finset ι)] with B hB
    have hi : i ∈ B := hB (Finset.mem_singleton_self i)
    show (0 : R i) = if i ∈ B then 0 else y i
    rw [if_pos hi]
  have h1 : f = RestrictedProduct.inclusion R A hS ∘ g :=
    funext fun B => RestrictedProduct.ext _ _ fun i => hf B i
  have h2 : z = RestrictedProduct.inclusion R A hS o := RestrictedProduct.ext _ _ fun i => hz i
  rw [h1, h2]
  exact ((RestrictedProduct.continuous_inclusion hS).tendsto o).comp hg
private theorem UpperTheory.Reformulated.B.Qi11.sglS_apply {F : Type} [Field F] [NumberField F]
    (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    UpperTheory.Reformulated.B.Qi11.sglS A w = if w ∈ A then 1 else 0 := by
  induction A using Finset.induction_on with
  | empty => rfl
  | insert v A hv ih =>
    have h : UpperTheory.Reformulated.B.Qi11.sglS (insert v A) =
        UpperTheory.Reformulated.B.Qi11.sglV v 1 + UpperTheory.Reformulated.B.Qi11.sglS A := Finset.sum_insert hv
    have h' : UpperTheory.Reformulated.B.Qi11.sglS (insert v A) w =
        (Pi.single v 1 : ∀ u, IsDedekindDomain.HeightOneSpectrum.adicCompletion F u) w +
          UpperTheory.Reformulated.B.Qi11.sglS A w := by
      rw [h]
      rfl
    rw [h', ih]
    by_cases hw : w = v
    · subst hw
      simp [hv]
    · simp [hw]
end

set_option autoImplicit false
open scoped Classical
namespace UpperTheory.Reformulated.B.Qi11
theorem _root_.solution :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (y : UpperTheory.Reformulated.B.Qi11.Af F),
      Filter.Tendsto
        (fun (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) ↦
          ((1 : UpperTheory.Reformulated.B.Qi11.Af F) - UpperTheory.Reformulated.B.Qi11.sglS A) * y)
        Filter.atTop (nhds (0 : UpperTheory.Reformulated.B.Qi11.Af F)) := by
  intro F _ _ y
  have key := UpperTheory.Reformulated.B.Qi11.tendsto_cut
    (R := fun v => IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)
    (A := fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
      SetLike.coe (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v))
    (fun v => zero_mem _)
  refine key y (0 : UpperTheory.Reformulated.B.Qi11.Af F) (fun w => ?_)
    (fun B => ((1 - UpperTheory.Reformulated.B.Qi11.sglS B) * y : UpperTheory.Reformulated.B.Qi11.Af F)) fun B w => ?_
  · rfl
  · show (1 - UpperTheory.Reformulated.B.Qi11.sglS B w) * y w = if w ∈ B then 0 else y w
    rw [UpperTheory.Reformulated.B.Qi11.sglS_apply]
    split_ifs <;> simp
end UpperTheory.Reformulated.B.Qi11
