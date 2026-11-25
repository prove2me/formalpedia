-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qi13.linIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:59:35.261498+00:00
-- url     : https://prove2.me/submissions/bc9e5016-cdec-4200-bac2-e7deb8d94e2c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemOfClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Qi13.key {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Algebra ℚ_[l] K]
    (O : Subring K) {k : Type} [CommRing k] [Algebra (ZMod l) k] (r : O →+* k)
    (hO : ∀ c : ℤ_[l], algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O) {ι : Type} [Fintype ι] (x : ι → O)
    (h : LinearIndependent (ZMod l) (fun i => r (x i))) :
    LinearIndependent ℚ_[l] (fun i => (x i : K)) := by
  classical
  let φ : ℤ_[l] →+* O :=
    ((algebraMap ℚ_[l] K).comp PadicInt.Coe.ringHom).codRestrict O hO
  have hφ : ∀ c : ℤ_[l], r (φ c) = algebraMap (ZMod l) k (PadicInt.toZMod c) := by
    intro c
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (PadicInt.toZMod c)
    have hker : c - (n : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, hn, sub_self]
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hker
    obtain ⟨d, hd⟩ := hker
    have hl : (l : k) = 0 := by
      rw [← map_natCast (algebraMap (ZMod l) k), ZMod.natCast_self, map_zero]
    have hc : c = n + l * d := by rw [← hd]; ring
    rw [← hn, hc]
    simp only [map_add, map_mul, map_natCast, hl, zero_mul, add_zero]
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hne
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun i => ‖g i‖) ⟨i₀, Finset.mem_univ _⟩
  have hpos : 0 < ‖g m‖ := (norm_pos_iff.mpr hi₀).trans_le (hm i₀ (Finset.mem_univ _))
  have hgm : g m ≠ 0 := norm_pos_iff.mp hpos
  let c : ι → ℤ_[l] := fun i => ⟨g i / g m, by
    rw [norm_div]
    exact (div_le_one hpos).mpr (hm i (Finset.mem_univ _))⟩
  have hsum : ∑ i, φ (c i) * x i = 0 := by
    apply Subtype.ext
    have h1 : ∀ i, ((φ (c i) * x i : O) : K) = (g m)⁻¹ • (g i • (x i : K)) := by
      intro i
      change algebraMap ℚ_[l] K (g i / g m) * (x i : K) = _
      rw [smul_smul, Algebra.smul_def, div_eq_inv_mul]
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [h1]
    rw [← Finset.smul_sum, hg, smul_zero]
    rfl
  have hred : ∑ i, PadicInt.toZMod (c i) • r (x i) = 0 := by
    have h2 := congrArg r hsum
    rw [map_sum, map_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hφ, Algebra.smul_def]
  have h3 := h _ hred m
  have h4 : c m = 1 := Subtype.ext (div_self hgm)
  rw [h4, map_one] at h3
  exact one_ne_zero h3
private theorem UpperTheory.Reformulated.B.Qi13.mem_of_closed {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [TopologicalSpace K] [Algebra ℚ_[l] K] (O : Subring K) (hO : IsClosed (O : Set K))
    (hc : Continuous (algebraMap ℚ_[l] K)) (c : ℤ_[l]) :
    algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O := by
  refine PadicInt.denseRange_natCast.induction_on
    (p := fun c : ℤ_[l] => algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O) c ?_ ?_
  · exact hO.preimage (hc.comp continuous_subtype_val)
  · intro n
    rw [PadicInt.coe_natCast, map_natCast]
    exact natCast_mem O n
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qi13
theorem _root_.solution :
    ∀ (K : Type) [inst : Field K]
      [inst_1 :
        @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
      [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
      [inst_4 : Fact (Nat.Prime l)]
      [inst_5 :
        @Algebra (@Padic l inst_4) K
          (@Semifield.toCommSemiring (@Padic l inst_4) (@Field.toSemifield (@Padic l inst_4) (@instFieldPadic l inst_4)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
      [inst_6 :
        @CharP
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@IsDiscreteValuationRing.toIsLocalRing
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@instIsDomain K (@Field.toSemifield K inst))
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation K
                inst inst_1 inst_2 inst_3)))
          (@AddGroupWithOne.toAddMonoidWithOne
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@IsDiscreteValuationRing.toIsLocalRing
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@instIsDomain K (@Field.toSemifield K inst))
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                  K inst inst_1 inst_2 inst_3)))
            (@Ring.toAddGroupWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@IsDiscreteValuationRing.toIsLocalRing
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@instIsDomain K (@Field.toSemifield K inst))
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                    K inst inst_1 inst_2 inst_3)))
              (@DivisionRing.toRing
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@IsDiscreteValuationRing.toIsLocalRing
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@instIsDomain K (@Field.toSemifield K inst))
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                      K inst inst_1 inst_2 inst_3)))
                (@Field.toDivisionRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@IsDiscreteValuationRing.toIsLocalRing
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@instIsDomain K (@Field.toSemifield K inst))
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                        K inst inst_1 inst_2 inst_3)))
                  (@IsLocalRing.ResidueField.field
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@IsDiscreteValuationRing.toIsLocalRing
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@instIsDomain K (@Field.toSemifield K inst))
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                        K inst inst_1 inst_2 inst_3)))))))
          l],
      @Continuous (@Padic l inst_4) K
          (@UniformSpace.toTopologicalSpace (@Padic l inst_4)
            (@PseudoMetricSpace.toUniformSpace (@Padic l inst_4)
              (@SeminormedRing.toPseudoMetricSpace (@Padic l inst_4)
                (@SeminormedCommRing.toSeminormedRing (@Padic l inst_4)
                  (@NormedCommRing.toSeminormedCommRing (@Padic l inst_4)
                    (@NormedField.toNormedCommRing (@Padic l inst_4) (@Padic.normedField l inst_4)))))))
          inst_2
          (@DFunLike.coe
            (@RingHom (@Padic l inst_4) K
              (@Semiring.toNonAssocSemiring (@Padic l inst_4)
                (@CommSemiring.toSemiring (@Padic l inst_4)
                  (@Semifield.toCommSemiring (@Padic l inst_4)
                    (@Field.toSemifield (@Padic l inst_4) (@instFieldPadic l inst_4)))))
              (@Semiring.toNonAssocSemiring K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Padic l inst_4) (fun (x : @Padic l inst_4) ↦ K)
            (@RingHom.instFunLike (@Padic l inst_4) K
              (@Semiring.toNonAssocSemiring (@Padic l inst_4)
                (@CommSemiring.toSemiring (@Padic l inst_4)
                  (@Semifield.toCommSemiring (@Padic l inst_4)
                    (@Field.toSemifield (@Padic l inst_4) (@instFieldPadic l inst_4)))))
              (@Semiring.toNonAssocSemiring K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Algebra.algebraMap (@Padic l inst_4) K
              (@Semifield.toCommSemiring (@Padic l inst_4)
                (@Field.toSemifield (@Padic l inst_4) (@instFieldPadic l inst_4)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))) inst_5)) →
        @LinearIndependent (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_6)) (@Padic l inst_4) K
          (fun (i : Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_6)) ↦
            @Subtype.val K
              (fun (x : K) ↦
                @Membership.mem K
                  (@Subring K (@Ring.toNonAssocRing K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
                  (@SetLike.instMembership
                    (@Subring K (@Ring.toNonAssocRing K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))) K
                    (@Subring.instSetLike K
                      (@Ring.toNonAssocRing K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))))
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))
                  x)
              (@UpperTheory.Reformulated.B.Qi13.blift K inst inst_1 inst_2 inst_3 l inst_4 inst_6 i))
          (@DivisionSemiring.toSemiring (@Padic l inst_4)
            (@Semifield.toDivisionSemiring (@Padic l inst_4)
              (@Field.toSemifield (@Padic l inst_4) (@instFieldPadic l inst_4))))
          (@Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Algebra.toModule (@Padic l inst_4) K
            (@Semifield.toCommSemiring (@Padic l inst_4) (@Field.toSemifield (@Padic l inst_4) (@instFieldPadic l inst_4)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))) inst_5) := by
  intro K _ _ _ _ l _ _ _ hc
  letI := UpperTheory.Reformulated.B.Qi13.algRes K l
  refine UpperTheory.Reformulated.B.Qi13.key (ValuativeRel.valuation K).integer
    (IsLocalRing.residue (ValuativeRel.valuation K).integer)
    (UpperTheory.Reformulated.B.Qi13.mem_of_closed _ Valuation.isClosed_integer hc)
    (UpperTheory.Reformulated.B.Qi13.blift K l) ?_
  have h : (fun i => IsLocalRing.residue (ValuativeRel.valuation K).integer
      (UpperTheory.Reformulated.B.Qi13.blift K l i)) = UpperTheory.Reformulated.B.Qi13.bb K l :=
    funext fun i => (UpperTheory.Reformulated.B.Qi13.aux8 K l i).choose_spec
  rw [h]
  exact (UpperTheory.Reformulated.B.Qi13.bb K l).linearIndependent
end UpperTheory.Reformulated.B.Qi13
