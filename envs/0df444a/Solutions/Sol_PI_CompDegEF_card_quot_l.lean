-- Prove2me | solution 1 for PI.CompDegEF.card_quot_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:49.985827+00:00
-- url     : https://prove2.me/submissions/330e0269-122f-4f3d-842f-63ec350ffe01

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_MemIntegralClosureIffMemBall
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
variable {l : ℕ} [hl : Fact l.Prime]
namespace PI.CompDegEF
theorem _root_.solution {C : Type} [CommRing C] [Algebra ℤ_[l] C] {n : ℕ} (b : Basis (Fin n) ℤ_[l] C) :
    Nat.card (C ⧸ Ideal.span {((l : ℕ) : C)}) = l ^ n := by
  let f : C →+ (Fin n → ZMod l) :=
    AddMonoidHom.pi fun i =>
      (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toAddMonoidHom.comp (b.coord i).toAddMonoidHom
  have hf : ∀ x i, f x i = PadicInt.toZMod (b.repr x i) := fun x i => rfl
  have hsurj : Function.Surjective f := by
    intro w
    refine ⟨b.equivFun.symm (fun i => ((w i).val : ℤ_[l])), funext fun i => ?_⟩
    rw [hf]
    have h1 : b.repr (b.equivFun.symm (fun i => ((w i).val : ℤ_[l]))) i = ((w i).val : ℤ_[l]) := by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [h1, map_natCast, ZMod.natCast_zmod_val]
  have hlC : ((l : ℕ) : C) = algebraMap ℤ_[l] C (l : ℤ_[l]) := (map_natCast _ _).symm
  have hk : (Ideal.span {((l : ℕ) : C)}).toAddSubgroup = f.ker := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker]
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩
      funext i
      show f (y * ((l : ℕ) : C)) i = 0
      rw [hf, hlC, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
        map_natCast, ZMod.natCast_self, zero_mul]
    · intro hx
      have hdiv : ∀ i, ∃ d : ℤ_[l], b.repr x i = (l : ℤ_[l]) * d := fun i => by
        have h0 : PadicInt.toZMod (b.repr x i) = 0 := congrFun hx i
        have hm : b.repr x i ∈ Ideal.span {((l : ℕ) : ℤ_[l])} := by
          rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
          exact RingHom.mem_ker.mpr h0
        exact (Ideal.mem_span_singleton'.mp hm).imp fun d hd => by rw [← hd, mul_comm]
      choose d hd using hdiv
      refine ⟨∑ i, d i • b i, ?_⟩
      rw [hlC, mul_comm, ← Algebra.smul_def, Finset.smul_sum]
      conv_rhs => rw [← b.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd, smul_smul]
  have hcard : Nat.card (C ⧸ Ideal.span {((l : ℕ) : C)}) = Nat.card (C ⧸ f.ker) := by
    rw [← hk]; rfl
  rw [hcard, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv]
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
end PI.CompDegEF
