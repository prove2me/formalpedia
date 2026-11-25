-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.exists_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:39:22.445573+00:00
-- url     : https://prove2.me/submissions/789ceca1-98ca-47e9-b3d1-870325ee6f0a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPow
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_inR_self
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_inR_pow
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    {t : v.adicCompletion I.F} (htO : t ∈ v.adicCompletionIntegers I.F)
    (ht : α * α = incL I v t * α - 1) (N : ℕ) (hN : 0 < N) :
    ∃ i j : ℕ, i < j ∧ ∃ w, InR I v α w ∧ α ^ j - α ^ i = incL I v N * w := by
  classical
  have hpow : ∀ m : ℕ, InR I v α (α ^ m) := fun m => inR_pow I v α htO ht (inR_self I v α) m
  choose a b ha hb hab using hpow
  have hNF : (N : v.adicCompletion I.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let NO : Set (v.adicCompletion I.F) :=
    (fun y => (N : v.adicCompletion I.F) * y) '' (v.adicCompletionIntegers I.F : Set _)
  have hOo : IsOpen (v.adicCompletionIntegers I.F : Set (v.adicCompletion I.F)) :=
    Valued.isOpen_integer (R := v.adicCompletion I.F)
  have hNO : IsOpen NO := (Homeomorph.mulLeft₀ (N : v.adicCompletion I.F) hNF).isOpenMap _ hOo
  let U : v.adicCompletionIntegers I.F → Set (v.adicCompletion I.F) :=
    fun x => (fun y => y - (x : v.adicCompletion I.F)) ⁻¹' NO
  have hU : ∀ x, IsOpen (U x) := fun x => hNO.preimage (continuous_id.sub continuous_const)
  have hcov : (v.adicCompletionIntegers I.F : Set (v.adicCompletion I.F)) ⊆ ⋃ x, U x := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    exact ⟨0, zero_mem _, by simp⟩
  obtain ⟨T, hT⟩ := (PI.WAU.isCompact_Ov v).elim_finite_subcover U hU hcov
  have hsel : ∀ y ∈ (v.adicCompletionIntegers I.F : Set (v.adicCompletion I.F)),
      ∃ x : T, y ∈ U x := by
    intro y hy
    have := hT hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hx, hyx⟩ := this
    exact ⟨⟨x, hx⟩, hyx⟩
  choose sel hsel' using hsel
  let f : ℕ → T × T := fun m => (sel (a m) (ha m), sel (b m) (hb m))
  have key : ∀ i j, f i = f j → ∃ w, InR I v α w ∧ α ^ j - α ^ i = incL I v N * w := by
    intro i j hij
    have h1 : sel (a i) (ha i) = sel (a j) (ha j) := congrArg Prod.fst hij
    have h2 : sel (b i) (hb i) = sel (b j) (hb j) := congrArg Prod.snd hij
    obtain ⟨p1, hp1, e1⟩ := hsel' (a i) (ha i)
    obtain ⟨p2, hp2, e2⟩ := hsel' (a j) (ha j)
    obtain ⟨q1, hq1, f1⟩ := hsel' (b i) (hb i)
    obtain ⟨q2, hq2, f2⟩ := hsel' (b j) (hb j)
    rw [h1] at e1
    rw [h2] at f1
    refine ⟨incL I v (p2 - p1) + incL I v (q2 - q1) * α,
      ⟨p2 - p1, q2 - q1, sub_mem hp2 hp1, sub_mem hq2 hq1, rfl⟩, ?_⟩
    have ea : a j - a i = (N : v.adicCompletion I.F) * (p2 - p1) := by
      simp only at e1 e2
      linear_combination e1 - e2
    have eb : b j - b i = (N : v.adicCompletion I.F) * (q2 - q1) := by
      simp only at f1 f2
      linear_combination f1 - f2
    have ea' := congrArg (incL I v) ea
    have eb' := congrArg (incL I v) eb
    simp only [map_sub, map_mul, map_natCast] at ea' eb' ⊢
    rw [hab j, hab i]
    linear_combination ea' + α * eb'
  obtain ⟨i, j, hne, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨i, j, h, key i j hf⟩
  · exact ⟨j, i, h, key j i hf.symm⟩
end PI.UnitaryGroupMassFormula.AdIndexEq
