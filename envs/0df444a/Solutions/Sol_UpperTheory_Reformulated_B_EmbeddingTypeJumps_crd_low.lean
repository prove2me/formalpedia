-- Prove2me | solution 1 for UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:33.355436+00:00
-- url     : https://prove2.me/submissions/7c8311d9-3b8d-49ea-951b-2155f78f691b

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EmbeddingTypeJumps
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


section
private theorem UpperTheory.Reformulated.B.EmbeddingTypeJumps.integral_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E]
    (W : Formalism.BasicNotions.HSpace E) {a : E} (ha : IsIntegral ℤ a) {v : W.V} (hv : v ∈ W.L0) :
    a • v ∈ W.L0 := by
  let b : NumberField.RingOfIntegers E := ⟨a, ha⟩
  have h : (algebraMap (NumberField.RingOfIntegers E) E b) • v ∈ W.L0 := by
    rw [algebraMap_smul]
    exact W.L0.smul_mem b hv
  exact h
private theorem UpperTheory.Reformulated.B.EmbeddingTypeJumps.exists_int_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E]
    (W : Formalism.BasicNotions.HSpace E) (v : W.V) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ W.L0 := by
  have hv : v ∈ Submodule.span E (W.L0 : Set W.V) := by
    rw [W.standardTuple_isLattice.span_eq_top]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨n, hn, hy⟩ := hy
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have h : ((m * n : ℤ) : E) • (x + y) = n • ((m : E) • x) + m • ((n : E) • y) := by
      rw [← Int.cast_smul_eq_zsmul E n, ← Int.cast_smul_eq_zsmul E m, smul_smul, smul_smul,
        smul_add, Int.cast_mul, mul_comm (n : E)]
    rw [h]
    exact W.L0.add_mem (zsmul_mem hx n) (zsmul_mem hy m)
  | smul a x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    have ha : IsAlgebraic ℤ a :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨m, hm, hint⟩ := ha.exists_integral_multiple
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have hmem := UpperTheory.Reformulated.B.EmbeddingTypeJumps.integral_smul_mem W hint hx
    have h : ((m * n : ℤ) : E) • a • x = (m • a) • ((n : E) • x) := by
      rw [smul_smul, smul_smul, zsmul_eq_mul, Int.cast_mul]
      congr 1
      ring
    rw [h]
    exact hmem
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.EmbeddingTypeJumps
theorem _root_.solution :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E]
      [inst_5 : StarRing E] (W : Formalism.BasicNotions.HSpace E),
      ∃ (c : NumberField.RingOfIntegers F),
        c ≠ (0 : NumberField.RingOfIntegers F) ∧
          ∀ (i : Fin W.rank) (e : E), IsIntegral ℤ e → Pi.single i ((↑c : F) • e) ∈ UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd W := by
  intro F E _ _ _ _ _ _ W
  choose n hn hmem using fun i : Fin W.rank => UpperTheory.Reformulated.B.EmbeddingTypeJumps.exists_int_smul_mem W (W.frame i)
  refine ⟨((∏ i, n i : ℤ) : NumberField.RingOfIntegers F), ?_, ?_⟩
  · exact Int.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hn i)
  · intro i e he
    obtain ⟨k, hk⟩ : n i ∣ ∏ j, n j := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    have hk' : IsIntegral ℤ (k • e) := he.smul k
    have hm := UpperTheory.Reformulated.B.EmbeddingTypeJumps.integral_smul_mem W hk' (hmem i)
    have hc : ((((∏ j, n j : ℤ) : NumberField.RingOfIntegers F) : F)) • e = (k • e) * (n i : E) := by
      rw [hk, Algebra.smul_def, NumberField.RingOfIntegers.coe_eq_algebraMap, map_intCast,
        map_intCast, zsmul_eq_mul, Int.cast_mul]
      ring
    show ∑ j : Fin W.rank, (Pi.single i _ : Fin W.rank → E) j • W.frame j ∈ W.L0
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, hc, mul_smul]
    exact hm
end UpperTheory.Reformulated.B.EmbeddingTypeJumps
