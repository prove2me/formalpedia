-- Prove2me | solution 1 for QuaternionAlgebra.inv_mul_mem_finiteAdeleBox_and_smul_mul_mem_of_mem_primeHeckeSet_of_conjByFiniteIdele_meetOrder_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/75e9903b-59a0-5754-804a-371adc543852

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_Submodule_finiteAdeleBox_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_inv_mul_mem_finiteAdeleBox_and_smul_mul_mem_of_mem_primeHeckeSet_of_conjByFiniteIdele_meetOrder_eq
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace ALPin

section Places

def place (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

variable (q : ℕ) (hq : q.Prime)

local notation "𝔳" => place q hq
local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)

theorem primesEquiv_place : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) 𝔳 = ⟨q, hq⟩ := by
  simp [place]

theorem natGenerator_place : Rat.HeightOneSpectrum.natGenerator 𝔳 = q :=
  congrArg Subtype.val (primesEquiv_place q hq)

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natCast_mem_asIdeal_place_iff (n : ℕ) : (n : 𝓞 ℚ) ∈ (𝔳).asIdeal ↔ q ∣ n := by
  rw [natCast_mem_asIdeal_iff, natGenerator_place]

theorem q_mem_asIdeal : (q : 𝓞 ℚ) ∈ (𝔳).asIdeal := (natCast_mem_asIdeal_place_iff q hq q).2 dvd_rfl

theorem q_notMem_asIdeal_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) : (q : 𝓞 ℚ) ∉ w.asIdeal := by
  rw [natCast_mem_asIdeal_iff]
  intro h
  have : Rat.HeightOneSpectrum.natGenerator w = q :=
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hq).mp h
  apply hw
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  rw [primesEquiv_place]
  exact Subtype.ext this

theorem valuation_natCast_eq_one_of_notMem (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 hn

theorem valuation_q_eq_one_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) : w.valuation ℚ (q : ℚ) = 1 :=
  valuation_natCast_eq_one_of_notMem w q (q_notMem_asIdeal_of_ne q hq w hw)

theorem valuation_natCast_eq_one_of_not_dvd (n : ℕ) (hn : ¬ q ∣ n) : (𝔳).valuation ℚ (n : ℚ) = 1 :=
  valuation_natCast_eq_one_of_notMem _ n (mt (natCast_mem_asIdeal_place_iff q hq n).1 hn)

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem algebraMap_natCast (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ) = (n : w.adicCompletion ℚ) := map_natCast _ n

theorem natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← algebraMap_natCast, valued_algebraMap,
    show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one w _

theorem inv_natCast_mem_integers_of_valuation (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ)
    (hc : w.valuation ℚ (c : ℚ) = 1) : ((c : ℕ) : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ← algebraMap_natCast, valued_algebraMap, hc, inv_one]

theorem inv_q_mem_integers_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) :
    ((q : ℕ) : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ :=
  inv_natCast_mem_integers_of_valuation w q (valuation_q_eq_one_of_ne q hq w hw)

theorem natCast_ne_zero_of_valuation (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ) (hc : w.valuation ℚ (c : ℚ) = 1) :
    ((c : ℕ) : w.adicCompletion ℚ) ≠ 0 := by
  intro h
  have := valued_algebraMap w (c : ℚ)
  rw [algebraMap_natCast, h, map_zero, hc] at this
  exact zero_ne_one this

theorem asIdeal_place_eq_span : (𝔳).asIdeal = Ideal.span {(q : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) 𝔳
  rw [natGenerator_place] at h
  have h2 : (𝔳).asIdeal = Ideal.map ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ)
      (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) (𝔳).asIdeal) := by
    rw [Ideal.map_map]
    have : ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ).comp
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) = RingHom.id _ := by
      ext x; simp
    rw [this, Ideal.map_id]
  rw [h2]
  erw [← h]
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  simp

theorem valuation_q : (𝔳).valuation ℚ (q : ℚ) = WithZero.exp (-1) := by
  rw [show (q : ℚ) = algebraMap (𝓞 ℚ) ℚ (q : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ (by exact_mod_cast hq.ne_zero) (asIdeal_place_eq_span q hq)

theorem valued_q : Valued.v ((q : ℕ) : 𝕂) = WithZero.exp (-1) := by
  rw [← algebraMap_natCast, valued_algebraMap, valuation_q]

theorem q_ne_zero' : ((q : ℕ) : 𝕂) ≠ 0 := by
  intro h
  have := valued_q q hq
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem q_mem_integers : ((q : ℕ) : 𝕂) ∈ 𝓞v := natCast_mem_integers (𝔳) q

theorem valued_le_one_of_mem {x : 𝕂} (hx : x ∈ 𝓞v) : Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ (𝔳)).1 hx

theorem mem_integers_of_valued_le_one {x : 𝕂} (hx : Valued.v x ≤ 1) : x ∈ 𝓞v :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ (𝔳)).2 hx

theorem inv_q_notMem_integers : ((q : ℕ) : 𝕂)⁻¹ ∉ 𝓞v := by
  intro h
  have := valued_le_one_of_mem q hq h
  rw [map_inv₀, valued_q, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
  norm_num at this

theorem q_inv_mul_mem_integers_iff {x : 𝕂} (hx : x ∈ 𝓞v) :
    ((q : ℕ) : 𝕂)⁻¹ * x ∈ 𝓞v ↔ Valued.v x < 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, valued_q]
  by_cases hx0 : x = 0
  · simp [hx0]
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m :=
      ⟨WithZero.log (Valued.v x), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx0)).symm⟩
    rw [hm, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp,
      WithZero.exp_lt_exp]
    omega

theorem inv_mem_integers_of_valued_eq_one {x : 𝕂} (h : Valued.v x = 1) : x⁻¹ ∈ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]

theorem inv_mem_or_q_inv_mul_mem {x : 𝕂} (hx : x ∈ 𝓞v) :
    x⁻¹ ∈ 𝓞v ∨ ((q : ℕ) : 𝕂)⁻¹ * x ∈ 𝓞v := by
  rcases (valued_le_one_of_mem q hq hx).lt_or_eq with h | h
  · exact Or.inr ((q_inv_mul_mem_integers_iff q hq hx).2 h)
  · exact Or.inl (inv_mem_integers_of_valued_eq_one q hq h)

theorem valued_eq_one_of_mul_eq_one {x y : 𝕂} (hx : x ∈ 𝓞v) (hy : y ∈ 𝓞v) (h : x * y = 1) :
    Valued.v x = 1 := by
  have h1 : Valued.v x * Valued.v y = 1 := by rw [← map_mul, h, map_one]
  have hx1 := valued_le_one_of_mem q hq hx
  have hy1 := valued_le_one_of_mem q hq hy
  by_contra hne
  have hlt : Valued.v x < 1 := lt_of_le_of_ne hx1 hne
  have : Valued.v x * Valued.v y < 1 := by
    calc Valued.v x * Valued.v y ≤ Valued.v x * 1 := mul_le_mul_right hy1 _
      _ = Valued.v x := mul_one _
      _ < 1 := hlt
  rw [h1] at this
  exact lt_irrefl _ this

end Places

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : 𝕂} (hc : c ∈ 𝓞v) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem tmul_one_mem_localBox {z : D} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : 𝕂) ∈ Submodule.localBox Λ v :=
  tmul_mem_localBox Λ v hz (one_mem _)

theorem localBox_mono {Λ Λ' : Submodule ℤ D} (h : Λ ≤ Λ') :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, h hz, c, hc, hx⟩

theorem localBox_le_of_forall_tmul_mem (S : AddSubgroup (D ⊗[ℚ] 𝕂))
    (h : ∀ z ∈ Λ, ∀ c : 𝕂, c ∈ 𝓞v → z ⊗ₜ[ℚ] c ∈ S) : Submodule.localBox Λ v ≤ S :=
  (AddSubgroup.closure_le _).2 fun _ ⟨z, hz, c, hc, hx⟩ => hx ▸ h z hz c hc

theorem one_tmul_mul_mem_localBox {x : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ v) {c : 𝕂}
    (hc : c ∈ 𝓞v) : ((1 : D) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tmul_mem_localBox Λ v hz (mul_mem hc hc')
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => exact (mul_neg _ x).symm ▸ neg_mem hx

theorem mul_mem_localBox (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    {x y : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  induction hy using AddSubgroup.closure_induction with
  | mem y' hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using AddSubgroup.closure_induction with
    | mem x' hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox Λ v (hmul _ _ hz' hz) (mul_mem hc' hc)
    | zero => rw [zero_mul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | neg x _ hx => exact (neg_mul x _).symm ▸ neg_mem hx
  | zero => rw [mul_zero]; exact zero_mem _
  | add x' y' _ _ hx' hy' => rw [mul_add]; exact add_mem hx' hy'
  | neg x' _ hx' => exact (mul_neg _ x').symm ▸ neg_mem hx'

omit Λ in
theorem ratCast_smul_eq_one_tmul_mul (r : ℚ) (x : D ⊗[ℚ] 𝕂) :
    r • x = ((1 : D) ⊗ₜ[ℚ] (algebraMap ℚ 𝕂 r)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z c =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

omit Λ in

theorem one_tmul_comm (c : 𝕂) (x : D ⊗[ℚ] 𝕂) : ((1 : D) ⊗ₜ[ℚ] c) * x = x * ((1 : D) ⊗ₜ[ℚ] c) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [mul_zero, zero_mul]
  | tmul z d => rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_comm]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

omit Λ in
theorem one_tmul_mul_one_tmul (c d : 𝕂) :
    ((1 : D) ⊗ₜ[ℚ] c) * ((1 : D) ⊗ₜ[ℚ] d) = (1 : D) ⊗ₜ[ℚ] (c * d) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

omit Λ v in
theorem one_tmul_one_eq (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((1 : D) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = (1 : D ⊗[ℚ] w.adicCompletion ℚ) := rfl

abbrev unitAt (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ :=
  Units.map (Submodule.finiteAdeleEvalAt D w).toRingHom.toMonoidHom g

omit Λ in
theorem coe_unitAt (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    ((unitAt w g : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ) : D ⊗[ℚ] w.adicCompletion ℚ) =
      Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] 𝔸f) := rfl

omit Λ in
theorem unitAt_mul (w : HeightOneSpectrum (𝓞 ℚ)) (g h : (D ⊗[ℚ] 𝔸f)ˣ) : unitAt w (g * h) = unitAt w g * unitAt w h :=
  map_mul _ _ _

omit Λ in
theorem unitAt_inv (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) : unitAt w g⁻¹ = (unitAt w g)⁻¹ :=
  map_inv _ _

omit Λ in
theorem coe_inv_unitAt (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    ((unitAt w g)⁻¹ : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ) =
      Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) := by
  rw [← map_inv]; rfl

omit Λ in
theorem ev_inv (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) =
      ((unitAt w g)⁻¹ : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ) := (coe_inv_unitAt w g).symm

omit Λ in
theorem ev_smul (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) (x : D ⊗[ℚ] 𝔸f) :
    Submodule.finiteAdeleEvalAt D w (r • x) =
      ((1 : D) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) r) * Submodule.finiteAdeleEvalAt D w x := by
  rw [map_smul, ratCast_smul_eq_one_tmul_mul]

theorem mem_finiteAdeleBox_iff (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤) (x : D ⊗[ℚ] 𝔸f) :
    x ∈ Submodule.finiteAdeleBox Λ ↔ ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Submodule.finiteAdeleEvalAt D w x ∈ Submodule.localBox Λ w :=
  Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hfg hspan x

theorem localBox_eq_of_nsmul_mem {A B : Submodule ℤ D} (hBA : B ≤ A) (c : ℕ)
    (hcA : ∀ z ∈ A, c • z ∈ B) (w : HeightOneSpectrum (𝓞 ℚ)) (hcw : w.valuation ℚ (c : ℚ) = 1) :
    Submodule.localBox A w = Submodule.localBox B w := by
  refine le_antisymm ?_ (localBox_mono w hBA)
  refine localBox_le_of_forall_tmul_mem A w _ fun z hz d hd => ?_
  have hc0 : (c : ℚ) ≠ 0 := by
    intro h; rw [h, map_zero] at hcw; exact zero_ne_one hcw
  have : z ⊗ₜ[ℚ] d = (((c : ℕ) : ℚ) • z) ⊗ₜ[ℚ] (((c : ℕ) : ℚ)⁻¹ • d) := by
    rw [TensorProduct.smul_tmul, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  rw [this, Nat.cast_smul_eq_nsmul]
  refine tmul_mem_localBox B w (hcA z hz) ?_
  rw [← algebraMap_smul (HeightOneSpectrum.adicCompletion ℚ w) ((c : ℚ)⁻¹) d, smul_eq_mul]
  refine mul_mem ?_ hd
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap, map_inv₀, hcw, inv_one]

theorem finiteAdeleBox_mono {A B : Submodule ℤ D} (h : A ≤ B) : Submodule.finiteAdeleBox A ≤ Submodule.finiteAdeleBox B :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, h hz, c, hc, hx⟩

omit Λ in
theorem ev_units_mul_inv (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] 𝔸f) *
      Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]

omit Λ in
theorem ev_units_inv_mul (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) *
      Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] 𝔸f) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

theorem mem_localBox_conj_iff (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (g : (D ⊗[ℚ] 𝔸f)ˣ) (w : HeightOneSpectrum (𝓞 ℚ)) (y : D ⊗[ℚ] w.adicCompletion ℚ) :
    y ∈ Submodule.localBox (Submodule.conjByFiniteIdele Λ g) w ↔
      Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) * y *
        Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] 𝔸f) ∈ Submodule.localBox Λ w := by
  rw [Submodule.mem_localBox_conjByFiniteIdele_iff Λ hfg hspan g w y]
  set gw := Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] 𝔸f)
  set gwi := Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f)
  have h1 : gw * gwi = 1 := ev_units_mul_inv w g
  have h2 : gwi * gw = 1 := ev_units_inv_mul w g
  constructor
  · rintro ⟨t, ht, rfl⟩
    have e : gwi * (gw * t * gwi) * gw = (gwi * gw) * t * (gwi * gw) := by noncomm_ring
    rw [e, h2, one_mul, mul_one]; exact ht
  · intro h
    refine ⟨_, h, ?_⟩
    calc y = (gw * gwi) * y * (gw * gwi) := by rw [h1, one_mul, mul_one]
      _ = gw * (gwi * y * gw) * gwi := by noncomm_ring

end Box

section LocalMatrix

variable (q : ℕ) (hq : q.Prime)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))
local notation "ϖ" => (((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ (place q hq)))

def intMat : Subring M₂ where
  carrier := {M | ∀ i j, M i j ∈ 𝓞v}
  mul_mem' {A B} hA hB i j := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => mul_mem (hA i k) (hB k j)
  one_mem' i j := by
    rw [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  add_mem' {A B} hA hB i j := by rw [Matrix.add_apply]; exact add_mem (hA i j) (hB i j)
  zero_mem' i j := by rw [Matrix.zero_apply]; exact zero_mem _
  neg_mem' {A} hA i j := by rw [Matrix.neg_apply]; exact neg_mem (hA i j)

theorem mem_intMat_iff (M : M₂) : M ∈ intMat q hq ↔ ∀ i j, M i j ∈ 𝓞v := Iff.rfl

theorem mem_intMat_iff' (M : M₂) :
    M ∈ intMat q hq ↔ M 0 0 ∈ 𝓞v ∧ M 0 1 ∈ 𝓞v ∧ M 1 0 ∈ 𝓞v ∧ M 1 1 ∈ 𝓞v := by
  rw [mem_intMat_iff]
  simp only [Fin.forall_fin_two]
  tauto

theorem of_mem_intMat_iff (x₀₀ x₀₁ x₁₀ x₁₁ : 𝕂) :
    (!![x₀₀, x₀₁; x₁₀, x₁₁] : M₂) ∈ intMat q hq ↔ x₀₀ ∈ 𝓞v ∧ x₀₁ ∈ 𝓞v ∧ x₁₀ ∈ 𝓞v ∧ x₁₁ ∈ 𝓞v := by
  rw [mem_intMat_iff']
  simp

theorem smul_mem_intMat {c : 𝕂} (hc : c ∈ 𝓞v) {M : M₂} (hM : M ∈ intMat q hq) : c • M ∈ intMat q hq :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hM i j)

theorem det_mem_integers {M : M₂} (hM : M ∈ intMat q hq) : M.det ∈ 𝓞v := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

theorem adjugate_mem_intMat {M : M₂} (hM : M ∈ intMat q hq) : M.adjugate ∈ intMat q hq := by
  rw [Matrix.adjugate_fin_two]
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using hM 1 1
  · simpa using neg_mem (hM 0 1)
  · simpa using neg_mem (hM 1 0)
  · simpa using hM 0 0

theorem eq_smul_adjugate {M Mi : M₂} (h1 : M * Mi = 1) (h2 : Mi * M = 1) :
    Mi = M.det⁻¹ • M.adjugate := by
  have hdet : M.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have key : Mi * (M * M.adjugate) = M.det • Mi := by
    rw [Matrix.mul_adjugate, Matrix.mul_smul, mul_one]
  rw [← mul_assoc, h2, one_mul] at key
  rw [key, smul_smul, inv_mul_cancel₀ hdet, one_smul]

theorem det_mul_det_eq_one {M Mi : M₂} (h1 : M * Mi = 1) : M.det * Mi.det = 1 := by
  rw [← Matrix.det_mul, h1, Matrix.det_one]

theorem valued_det_eq_one {M Mi : M₂} (hM : M ∈ intMat q hq) (hMi : Mi ∈ intMat q hq) (h1 : M * Mi = 1) :
    Valued.v M.det = 1 :=
  valued_eq_one_of_mul_eq_one q hq (det_mem_integers q hq hM) (det_mem_integers q hq hMi) (det_mul_det_eq_one q hq h1)

theorem inv_mem_intMat_of_valued_det {M Mi : M₂} (hM : M ∈ intMat q hq) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hdet : Valued.v M.det = 1) : Mi ∈ intMat q hq := by
  rw [eq_smul_adjugate q hq h1 h2]
  exact smul_mem_intMat q hq (inv_mem_integers_of_valued_eq_one q hq hdet) (adjugate_mem_intMat q hq hM)

theorem conj_mem_intMat_iff {P Pi Y : M₂} (hP : P ∈ intMat q hq) (hPi : Pi ∈ intMat q hq)
    (h1 : P * Pi = 1) (h2 : Pi * P = 1) : Pi * Y * P ∈ intMat q hq ↔ Y ∈ intMat q hq := by
  refine ⟨fun h => ?_, fun hY => (intMat q hq).mul_mem ((intMat q hq).mul_mem hPi hY) hP⟩
  have := (intMat q hq).mul_mem ((intMat q hq).mul_mem hP h) hPi
  have e : P * (Pi * Y * P) * Pi = (P * Pi) * Y * (P * Pi) := by noncomm_ring
  rwa [e, h1, one_mul, mul_one] at this

theorem mul_mem_intMat_iff_left {P Pi Y : M₂} (hP : P ∈ intMat q hq) (hPi : Pi ∈ intMat q hq)
    (h2 : Pi * P = 1) : P * Y ∈ intMat q hq ↔ Y ∈ intMat q hq := by
  refine ⟨fun h => ?_, fun hY => (intMat q hq).mul_mem hP hY⟩
  have := (intMat q hq).mul_mem hPi h
  rwa [← mul_assoc, h2, one_mul] at this

def tM : M₂ := !![1, 0; 0, ϖ]

def tMi : M₂ := !![1, 0; 0, ϖ⁻¹]

def E00 : M₂ := !![1, 0; 0, 0]
def E01 : M₂ := !![0, 1; 0, 0]
def E10 : M₂ := !![0, 0; 1, 0]
def E11 : M₂ := !![0, 0; 0, 1]

theorem tM_mul_tMi : tM q hq * tMi q hq = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tM, tMi, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ (q_ne_zero' q hq)]

theorem tMi_mul_tM : tMi q hq * tM q hq = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tM, tMi, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ (q_ne_zero' q hq)]

theorem tM_mem : tM q hq ∈ intMat q hq := by
  rw [tM, of_mem_intMat_iff]
  exact ⟨one_mem _, zero_mem _, zero_mem _, q_mem_integers q hq⟩

theorem det_tM : (tM q hq).det = ϖ := by simp [tM, Matrix.det_fin_two_of]

theorem tMi_mul (Y : M₂) : tMi q hq * Y = !![Y 0 0, Y 0 1; ϖ⁻¹ * Y 1 0, ϖ⁻¹ * Y 1 1] := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [tMi, Matrix.mul_apply, Fin.sum_univ_two]

theorem tM_mul (Y : M₂) : tM q hq * Y = !![Y 0 0, Y 0 1; ϖ * Y 1 0, ϖ * Y 1 1] := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [tM, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_tM (Y : M₂) : Y * tM q hq = !![Y 0 0, Y 0 1 * ϖ; Y 1 0, Y 1 1 * ϖ] := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [tM, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_tMi (Y : M₂) : Y * tMi q hq = !![Y 0 0, Y 0 1 * ϖ⁻¹; Y 1 0, Y 1 1 * ϖ⁻¹] := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [tMi, Matrix.mul_apply, Fin.sum_univ_two]

theorem tMi_mul_mul_tM (Y : M₂) :
    tMi q hq * Y * tM q hq = !![Y 0 0, Y 0 1 * ϖ; ϖ⁻¹ * Y 1 0, Y 1 1] := by
  rw [tMi_mul, mul_tM]
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp
  rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (q_ne_zero' q hq), one_mul]

theorem tM_mul_mul_tMi (Y : M₂) :
    tM q hq * Y * tMi q hq = !![Y 0 0, Y 0 1 * ϖ⁻¹; ϖ * Y 1 0, Y 1 1] := by
  rw [tM_mul, mul_tMi]
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp
  rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ (q_ne_zero' q hq), one_mul]

theorem tM_mul_mul_tM (Y : M₂) :
    tM q hq * Y * tM q hq = !![Y 0 0, Y 0 1 * ϖ; ϖ * Y 1 0, ϖ * Y 1 1 * ϖ] := by
  rw [tM_mul, mul_tM]
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp

theorem mul_E00_mul (A B : M₂) : A * E00 q hq * B = Matrix.of fun i j => A i 0 * B 0 j := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [E00, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_E01_mul (A B : M₂) : A * E01 q hq * B = Matrix.of fun i j => A i 0 * B 1 j := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [E01, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_E10_mul (A B : M₂) : A * E10 q hq * B = Matrix.of fun i j => A i 1 * B 0 j := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [E10, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_E11_mul (A B : M₂) : A * E11 q hq * B = Matrix.of fun i j => A i 1 * B 1 j := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [E11, Matrix.mul_apply, Fin.sum_univ_two]

theorem E00_mem : E00 q hq ∈ intMat q hq ∧ tMi q hq * E00 q hq * tM q hq ∈ intMat q hq := by
  refine ⟨?_, ?_⟩
  · rw [E00, of_mem_intMat_iff]; exact ⟨one_mem _, zero_mem _, zero_mem _, zero_mem _⟩
  · rw [tMi_mul_mul_tM, of_mem_intMat_iff]; simp [E00, one_mem, zero_mem]

theorem E01_mem : E01 q hq ∈ intMat q hq ∧ tMi q hq * E01 q hq * tM q hq ∈ intMat q hq := by
  refine ⟨?_, ?_⟩
  · rw [E01, of_mem_intMat_iff]; exact ⟨zero_mem _, one_mem _, zero_mem _, zero_mem _⟩
  · rw [tMi_mul_mul_tM, of_mem_intMat_iff]; simp [E01, one_mem, zero_mem, q_mem_integers q hq]

theorem E11_mem : E11 q hq ∈ intMat q hq ∧ tMi q hq * E11 q hq * tM q hq ∈ intMat q hq := by
  refine ⟨?_, ?_⟩
  · rw [E11, of_mem_intMat_iff]; exact ⟨zero_mem _, zero_mem _, zero_mem _, one_mem _⟩
  · rw [tMi_mul_mul_tM, of_mem_intMat_iff]; simp [E11, one_mem, zero_mem]

theorem E10_mem : E10 q hq ∈ intMat q hq := by
  rw [E10, of_mem_intMat_iff]; exact ⟨zero_mem _, zero_mem _, one_mem _, zero_mem _⟩

theorem tMi_E10_tM_notMem : tMi q hq * E10 q hq * tM q hq ∉ intMat q hq := by
  rw [tMi_mul_mul_tM, of_mem_intMat_iff]
  simp only [E10, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', mul_one, mul_zero, zero_mul]
  intro h
  exact inv_q_notMem_integers q hq h.2.2.1

theorem shapeA {μ μi : M₂} (h1 : μ * μi = 1) (hμ : μ ∈ intMat q hq) (hqμi : ϖ • μi ∈ intMat q hq)
    (hE : ∀ Y : M₂, Y ∈ intMat q hq → tMi q hq * Y * tM q hq ∈ intMat q hq → μi * Y * μ ∈ intMat q hq)
    (hF : μi * E10 q hq * μ ∉ intMat q hq) :
    tMi q hq * μ ∈ intMat q hq ∧ μi * tM q hq ∈ intMat q hq := by
  have hq0 := q_ne_zero' q hq

  have hA : ∀ i j, μi i 0 * μ 0 j ∈ 𝓞v := fun i j => by
    have := hE _ (E00_mem q hq).1 (E00_mem q hq).2 i j
    rwa [mul_E00_mul, Matrix.of_apply] at this
  have hC : ∀ i j, μi i 1 * μ 1 j ∈ 𝓞v := fun i j => by
    have := hE _ (E11_mem q hq).1 (E11_mem q hq).2 i j
    rwa [mul_E11_mul, Matrix.of_apply] at this
  have hF' : ∃ i j, μi i 1 * μ 0 j ∉ 𝓞v := by
    by_contra hall
    push Not at hall
    apply hF
    intro i j
    rw [mul_E10_mul, Matrix.of_apply]
    exact hall i j
  obtain ⟨i₀, j₀, ht⟩ := hF'
  have hb : ϖ * μi i₀ 1 ∈ 𝓞v := by
    have := hqμi i₀ 1
    rwa [Matrix.smul_apply, smul_eq_mul] at this
  have ha : μ 0 j₀ ∈ 𝓞v := hμ 0 j₀
  have ha0 : μ 0 j₀ ≠ 0 := by
    intro h; apply ht; rw [h, mul_zero]; exact zero_mem _
  have hc0 : μi i₀ 1 ≠ 0 := by
    intro h; apply ht; rw [h, zero_mul]; exact zero_mem _

  have hai : (μ 0 j₀)⁻¹ ∈ 𝓞v := by
    rcases inv_mem_or_q_inv_mul_mem q hq ha with h' | h'
    · exact h'
    · exfalso; apply ht
      have e : μi i₀ 1 * μ 0 j₀ = (ϖ * μi i₀ 1) * (ϖ⁻¹ * μ 0 j₀) := by
        field_simp
      rw [e]; exact mul_mem hb h'

  have hbi : (ϖ * μi i₀ 1)⁻¹ ∈ 𝓞v := by
    rcases inv_mem_or_q_inv_mul_mem q hq hb with h' | h'
    · exact h'
    · exfalso; apply ht
      rw [← mul_assoc, inv_mul_cancel₀ hq0, one_mul] at h'
      exact mul_mem h' ha

  have hcol : ∀ i, μi i 0 ∈ 𝓞v := fun i => by
    have := mul_mem (hA i j₀) hai
    rwa [mul_assoc, mul_inv_cancel₀ ha0, mul_one] at this

  have hrow : ∀ j, ϖ⁻¹ * μ 1 j ∈ 𝓞v := fun j => by
    have := mul_mem hbi (hC i₀ j)
    have e : (ϖ * μi i₀ 1)⁻¹ * (μi i₀ 1 * μ 1 j) = ϖ⁻¹ * μ 1 j := by
      field_simp
    rwa [e] at this
  refine ⟨?_, ?_⟩
  · rw [tMi_mul, of_mem_intMat_iff]
    exact ⟨hμ 0 0, hμ 0 1, hrow 0, hrow 1⟩
  · rw [mul_tM, of_mem_intMat_iff]
    refine ⟨hcol 0, ?_, hcol 1, ?_⟩
    · have := hqμi 0 1; rwa [Matrix.smul_apply, smul_eq_mul, mul_comm] at this
    · have := hqμi 1 1; rwa [Matrix.smul_apply, smul_eq_mul, mul_comm] at this

theorem varpi_inv_mul_apply_mem {k ki : M₂} (h1 : k * ki = 1) (hk : k ∈ intMat q hq) (hki : ki ∈ intMat q hq)
    (hN : ∀ Y : M₂, Y ∈ intMat q hq → tMi q hq * Y * tM q hq ∈ intMat q hq →
      tM q hq * (k * Y * ki) * tMi q hq ∈ intMat q hq) :
    ϖ⁻¹ * k 0 0 ∈ 𝓞v := by
  have e1 : k 0 0 * ki 0 1 * ϖ⁻¹ ∈ 𝓞v := by
    have := hN _ (E00_mem q hq).1 (E00_mem q hq).2 0 1
    rw [tM_mul_mul_tMi, mul_E00_mul] at this
    simpa using this
  have e2 : k 0 0 * ki 1 1 * ϖ⁻¹ ∈ 𝓞v := by
    have := hN _ (E01_mem q hq).1 (E01_mem q hq).2 0 1
    rw [tM_mul_mul_tMi, mul_E01_mul] at this
    simpa using this
  have hone : k 1 0 * ki 0 1 + k 1 1 * ki 1 1 = 1 := by
    have := congrFun (congrFun h1 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e : ϖ⁻¹ * k 0 0 = k 1 0 * (k 0 0 * ki 0 1 * ϖ⁻¹) + k 1 1 * (k 0 0 * ki 1 1 * ϖ⁻¹) := by
    calc ϖ⁻¹ * k 0 0 = ϖ⁻¹ * k 0 0 * (k 1 0 * ki 0 1 + k 1 1 * ki 1 1) := by rw [hone, mul_one]
      _ = _ := by ring
  rw [e]
  exact add_mem (mul_mem (hk 1 0) e1) (mul_mem (hk 1 1) e2)

def gM (k : M₂) : M₂ := ϖ⁻¹ • (tM q hq * k * tM q hq)

theorem gM_eq (k : M₂) : gM q hq k = !![ϖ⁻¹ * k 0 0, k 0 1; k 1 0, ϖ * k 1 1] := by
  have hq0 := q_ne_zero' q hq
  rw [gM, tM_mul_mul_tM]
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  · rw [mul_comm, mul_assoc, mul_inv_cancel₀ hq0, mul_one]
  · rw [← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
  · rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul, mul_comm]

theorem gM_mem {k : M₂} (hk : k ∈ intMat q hq) (h00 : ϖ⁻¹ * k 0 0 ∈ 𝓞v) : gM q hq k ∈ intMat q hq := by
  rw [gM_eq, of_mem_intMat_iff]
  exact ⟨h00, hk 0 1, hk 1 0, mul_mem (q_mem_integers q hq) (hk 1 1)⟩

theorem det_gM (k : M₂) : (gM q hq k).det = k.det := by
  have hq0 := q_ne_zero' q hq
  rw [gM_eq, Matrix.det_fin_two_of, Matrix.det_fin_two]
  field_simp

theorem gM_mul (k : M₂) : gM q hq k * k = ϖ⁻¹ • (tM q hq * k * (tM q hq * k)) := by
  rw [gM, smul_mul_assoc, mul_assoc]

end LocalMatrix

section RingLemmas

variable {T : Type*} [Ring T] (L : AddSubgroup T) (hmul : ∀ x y, x ∈ L → y ∈ L → x * y ∈ L)

include hmul in

theorem latB_local_at (A Ai B Bi c ci : T) (hA : A * Ai = 1) (hB : B * Bi = 1)
    (hc : c * ci = 1) (hcic : ∀ x, ci * x = x * ci)
    (hL3 : ci * (B * A) ∈ L) (hL4 : c * (Ai * Bi) ∈ L) (hL0 : c * Ai ∈ L) (Y : T) :
    Ai * Bi * Y ∈ L ↔ (Ai * Y ∈ L ∧ ci * Y ∈ L) := by
  constructor
  · intro h
    have h2 : ci * Y ∈ L := by
      have := hmul _ _ hL3 h
      have e : ci * (B * A) * (Ai * Bi * Y) = ci * Y := by
        calc _ = ci * (B * (A * Ai) * Bi) * Y := by noncomm_ring
          _ = ci * Y := by rw [hA, mul_one, hB, mul_one]
      rwa [e] at this
    refine ⟨?_, h2⟩
    have := hmul _ _ hL0 h2
    have e : c * Ai * (ci * Y) = Ai * Y := by
      calc _ = c * (Ai * ci) * Y := by noncomm_ring
        _ = c * (ci * Ai) * Y := by rw [hcic]
        _ = (c * ci) * Ai * Y := by noncomm_ring
        _ = Ai * Y := by rw [hc, one_mul]
    rwa [e] at this
  · rintro ⟨-, h2⟩
    have := hmul _ _ hL4 h2
    have e : c * (Ai * Bi) * (ci * Y) = Ai * Bi * Y := by
      calc _ = c * (Ai * Bi * ci) * Y := by noncomm_ring
        _ = c * (ci * (Ai * Bi)) * Y := by rw [hcic]
        _ = (c * ci) * (Ai * Bi) * Y := by noncomm_ring
        _ = _ := by rw [hc, one_mul]
    rwa [e] at this

include hmul in

theorem latB_local_away (A Ai B Bi ci : T) (hA : A * Ai = 1) (hB : B * Bi = 1)
    (hci : ∀ y ∈ L, ci * y ∈ L)
    (hAL : A ∈ L) (hC : Ai * B * A ∈ L) (hC' : Ai * Bi * A ∈ L) (Y : T) :
    Ai * Bi * Y ∈ L ↔ (Ai * Y ∈ L ∧ ci * Y ∈ L) := by
  constructor
  · intro h
    have h1 : Ai * Y ∈ L := by
      have := hmul _ _ hC h
      have e : Ai * B * A * (Ai * Bi * Y) = Ai * Y := by
        calc _ = Ai * (B * (A * Ai) * Bi) * Y := by noncomm_ring
          _ = Ai * Y := by rw [hA, mul_one, hB, mul_one]
      rwa [e] at this
    refine ⟨h1, ?_⟩
    have := hmul _ _ hAL h1
    rw [← mul_assoc, hA, one_mul] at this
    exact hci Y this
  · rintro ⟨h1, -⟩
    have := hmul _ _ hC' h1
    have e : Ai * Bi * A * (Ai * Y) = Ai * Bi * Y := by
      calc _ = Ai * Bi * (A * Ai) * Y := by noncomm_ring
        _ = _ := by rw [hA, mul_one]
    rwa [e] at this

end RingLemmas

section Frame

variable {a b : ℚ}

set_option quotPrecheck false in
local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]

theorem local_facts (q' : ℕ) (hq' : q'.Prime) (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (ℍ𝔸)ˣ) (hm : QuaternionAlgebra.IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m))
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : R = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m)
    (hRN : R.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N) (hq'q : ¬ q' ∣ N * q)
    (m' : (ℍ𝔸)ˣ)
    (hm'₁ : ((m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm'N : ((N * q : ℕ) : ℚ) • ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁)
    (S : Submodule ℤ ℍ[ℚ, a, b]) (hS : S = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m')
    (n : (ℍ𝔸)ˣ) (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    (hSn : S = CerednikDrinfeld.meetOrder R n) (hnorm : Submodule.conjByFiniteIdele S n = S) :
    (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ place q hq →
      ev w ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R w ∧
      ev w ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R w) ∧
    Submodule.localBox Λ₁ (place q hq) = Submodule.localBox R (place q hq) ∧
    ev (place q hq) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈
      Submodule.localBox Λ₁ (place q hq) ∧
    ev (place q hq) ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈
      Submodule.localBox Λ₁ (place q hq) ∧
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : (place q hq).adicCompletion ℚ)⁻¹) *
      (ev (place q hq) ((n : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈
      Submodule.localBox Λ₁ (place q hq) ∧
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : (place q hq).adicCompletion ℚ)) *
      (ev (place q hq) ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈
      Submodule.localBox Λ₁ (place q hq) ∧
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : (place q hq).adicCompletion ℚ)) *
      ev (place q hq) ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox Λ₁ (place q hq) ∧
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : (place q hq).adicCompletion ℚ)⁻¹) *
      (ev (place q hq) ((n : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈
      Submodule.localBox Λ₁ (place q hq) ∧
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : (place q hq).adicCompletion ℚ)) *
      (ev (place q hq) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈
      Submodule.localBox Λ₁ (place q hq) := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  set v : HeightOneSpectrum (𝓞 ℚ) := place q hq with hv

  have hΛo : QuaternionAlgebra.IsOrder Λ₁ := hΛ₁.1
  have hRo : QuaternionAlgebra.IsOrder R := by rw [hR]; exact hΛo.inf hm.1
  have hΛ'o : QuaternionAlgebra.IsOrder (Submodule.conjByFiniteIdele Λ₁ m') :=
    QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ₁ hΛo m'
  have hRno : QuaternionAlgebra.IsOrder (Submodule.conjByFiniteIdele R n) :=
    QuaternionAlgebra.IsOrder.conjByFiniteIdele R hRo n
  have hSo : QuaternionAlgebra.IsOrder S := by rw [hS]; exact hΛo.inf hΛ'o
  have hRΛ₁ : R ≤ Λ₁ := by rw [hR]; exact inf_le_left
  have hREich : QuaternionAlgebra.IsEichlerOrder R N := ⟨Λ₁, _, hΛ₁, hm, hR, hRN⟩

  have hNΛ₁ : ∀ z ∈ Λ₁, N • z ∈ R := by
    intro z hz
    have := AddSubgroup.nsmul_relIndex_mem R.toAddSubgroup (K := Λ₁.toAddSubgroup) hz
    rwa [hRN] at this
  have hRΛ_v : Submodule.localBox Λ₁ v = Submodule.localBox R v :=
    localBox_eq_of_nsmul_mem hRΛ₁ N hNΛ₁ v (valuation_natCast_eq_one_of_not_dvd q hq N hqN)

  have hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [hv, natCast_mem_asIdeal_place_iff]
    intro h
    obtain rfl : q = q' := (Nat.prime_dvd_prime_iff_eq hq hq').1 h
    exact hq'q (dvd_mul_left q N)
  have hNv : (N : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [hv, natCast_mem_asIdeal_place_iff]; exact hqN
  obtain ⟨hn_away, φ, hφ1, hφR, k₀, k₀i, hk₀, hk₀i, hkk, hkk', hν, hνi⟩ :=
    QuaternionAlgebra.exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet hdef hREich
      q hq v (q_mem_asIdeal q hq) hq'v hNv n hn
  have hφΛ : ∀ x, x ∈ Submodule.localBox Λ₁ v ↔ φ x ∈ intMat q hq := fun x => by
    rw [hRΛ_v]; exact hφR x
  have hk₀' : k₀ ∈ intMat q hq := hk₀
  have hk₀i' : k₀i ∈ intMat q hq := hk₀i
  have hν' : φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) = tM q hq * k₀ := hν
  have hνi' : φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) = k₀i * tMi q hq := hνi
  have hφc : ∀ (c : v.adicCompletion ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ),
      φ (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x) = c • φ x := fun c x => by
    rw [map_mul, hφ1, smul_mul_assoc, one_mul]
  have hq0 := q_ne_zero' q hq
  have hmulΛ : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) {x y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ},
      x ∈ Submodule.localBox Λ₁ w → y ∈ Submodule.localBox Λ₁ w → x * y ∈ Submodule.localBox Λ₁ w :=
    fun w x y hx hy => mul_mem_localBox Λ₁ w (fun _ _ h1 h2 => hΛo.mul_mem h1 h2) hx hy

  have hμμi : φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) = 1 := by
    rw [← map_mul, ev_units_mul_inv, map_one]
  have hμiμ : φ (ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)) = 1 := by
    rw [← map_mul, ev_units_inv_mul, map_one]
  have hννi : φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) = 1 := by
    rw [← map_mul, ev_units_mul_inv, map_one]
  have hνiν : φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) = 1 := by
    rw [← map_mul, ev_units_inv_mul, map_one]
  have hm'v : ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox Λ₁ v :=
    (mem_finiteAdeleBox_iff Λ₁ hΛo.fg hΛo.spanTop _).1 hm'₁ v
  have hμ : φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈ intMat q hq := (hφΛ _).1 hm'v

  have hL0 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : v.adicCompletion ℚ)) * ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈
      Submodule.localBox Λ₁ v := by
    have h1 := (mem_finiteAdeleBox_iff Λ₁ hΛo.fg hΛo.spanTop _).1 hm'N v
    rw [ev_smul, algebraMap_natCast] at h1
    have h2 := one_tmul_mul_mem_localBox Λ₁ v h1
      (inv_natCast_mem_integers_of_valuation v N (valuation_natCast_eq_one_of_not_dvd q hq N hqN))
    rw [← mul_assoc, one_tmul_mul_one_tmul] at h2
    convert h2 using 3
    all_goals try rfl
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ (natCast_ne_zero_of_valuation v N
      (valuation_natCast_eq_one_of_not_dvd q hq N hqN)), one_mul]
  have hqμi : ((q : ℕ) : v.adicCompletion ℚ) • φ (ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈ intMat q hq := by
    rw [← hφc]; exact (hφΛ _).1 hL0

  have hS1 : ∀ y, y ∈ Submodule.localBox S v ↔ y ∈ Submodule.localBox Λ₁ v ∧
      ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * y * ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox Λ₁ v := by
    intro y
    rw [hS, Submodule.localBox_inf Λ₁ (Submodule.conjByFiniteIdele Λ₁ m') hΛo.fg hΛo.spanTop hΛ'o.fg
      hΛ'o.spanTop v, AddSubgroup.mem_inf, mem_localBox_conj_iff Λ₁ hΛo.fg hΛo.spanTop m' v y]
  have hS2 : ∀ y, y ∈ Submodule.localBox S v ↔ y ∈ Submodule.localBox Λ₁ v ∧
      ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * y * ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox Λ₁ v := by
    intro y
    rw [hSn]
    unfold CerednikDrinfeld.meetOrder
    rw [Submodule.localBox_inf R (Submodule.conjByFiniteIdele R n) hRo.fg hRo.spanTop hRno.fg hRno.spanTop v,
      AddSubgroup.mem_inf, mem_localBox_conj_iff R hRo.fg hRo.spanTop n v y, hRΛ_v]

  have hnS : ∀ y ∈ Submodule.localBox S v,
      ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸) * y * ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox S v := by
    intro y hy
    have : ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸) * y * ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈
        Submodule.localBox (Submodule.conjByFiniteIdele S n) v :=
      (Submodule.mem_localBox_conjByFiniteIdele_iff S hSo.fg hSo.spanTop n v _).2 ⟨y, hy, rfl⟩
    rwa [hnorm] at this

  have hSmat : ∀ y, y ∈ Submodule.localBox S v ↔
      (φ y ∈ intMat q hq ∧ tMi q hq * φ y * tM q hq ∈ intMat q hq) := by
    intro y
    rw [hS2 y, hφΛ, hφΛ, map_mul, map_mul, hν', hνi']
    have e : k₀i * tMi q hq * φ y * (tM q hq * k₀) = k₀i * (tMi q hq * φ y * tM q hq) * k₀ := by noncomm_ring
    rw [e, conj_mem_intMat_iff q hq hk₀' hk₀i' hkk hkk']

  have hE : ∀ Y, Y ∈ intMat q hq → tMi q hq * Y * tM q hq ∈ intMat q hq →
      φ (ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * Y * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈ intMat q hq := by
    intro Y hY hYI
    have hyS : φ.symm Y ∈ Submodule.localBox S v := by
      rw [hSmat, RingEquiv.apply_symm_apply]; exact ⟨hY, hYI⟩
    have := ((hS1 _).1 hyS).2
    rw [hφΛ, map_mul, map_mul, RingEquiv.apply_symm_apply] at this
    exact this
  have hF : φ (ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * E10 q hq * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)) ∉ intMat q hq := by
    intro H
    have hyΛ : φ.symm (E10 q hq) ∈ Submodule.localBox Λ₁ v := by
      rw [hφΛ, RingEquiv.apply_symm_apply]; exact E10_mem q hq
    have hmy : ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * φ.symm (E10 q hq) * ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈
        Submodule.localBox Λ₁ v := by
      rw [hφΛ, map_mul, map_mul, RingEquiv.apply_symm_apply]; exact H
    have hyS : φ.symm (E10 q hq) ∈ Submodule.localBox S v := (hS1 _).2 ⟨hyΛ, hmy⟩
    have := ((hSmat _).1 hyS).2
    rw [RingEquiv.apply_symm_apply] at this
    exact tMi_E10_tM_notMem q hq this
  obtain ⟨hk₁, hk₁i⟩ := shapeA q hq hμμi hμ hqμi hE hF

  have hNB : ∀ Y, Y ∈ intMat q hq → tMi q hq * Y * tM q hq ∈ intMat q hq →
      tM q hq * (k₀ * Y * k₀i) * tMi q hq ∈ intMat q hq := by
    intro Y hY hYI
    have hyS : φ.symm Y ∈ Submodule.localBox S v := by
      rw [hSmat, RingEquiv.apply_symm_apply]; exact ⟨hY, hYI⟩
    have h2 := ((hS1 _).1 (hnS _ hyS)).1
    rw [hφΛ, map_mul, map_mul, hν', hνi', RingEquiv.apply_symm_apply] at h2
    have e : tM q hq * k₀ * Y * (k₀i * tMi q hq) = tM q hq * (k₀ * Y * k₀i) * tMi q hq := by noncomm_ring
    rwa [e] at h2
  have h00 := varpi_inv_mul_apply_mem q hq hkk hk₀' hk₀i' hNB
  have hg : gM q hq k₀ ∈ intMat q hq := gM_mem q hq hk₀' h00

  have hG_eq : ((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
      (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸))) =
      gM q hq k₀ * (tMi q hq * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸))) := by
    rw [hν', gM, smul_mul_assoc]
    congr 1
    calc tM q hq * k₀ * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸))
        = tM q hq * k₀ * (tM q hq * tMi q hq) * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)) := by rw [tM_mul_tMi, mul_one]
      _ = tM q hq * k₀ * tM q hq * (tMi q hq * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸))) := by noncomm_ring
  have hG : ((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
      (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸))) ∈ intMat q hq := by
    rw [hG_eq]; exact (intMat q hq).mul_mem hg hk₁
  have hGGi : (((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
      (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)))) *
      (((q : ℕ) : v.adicCompletion ℚ) •
        (φ (ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)))) = 1 := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hq0, one_smul]
    calc _ = φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * (φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)) *
        φ (ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by noncomm_ring
      _ = 1 := by rw [hμμi, mul_one, hννi]
  have hGiG : (((q : ℕ) : v.adicCompletion ℚ) •
        (φ (ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)))) *
      (((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
        (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)))) = 1 := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hq0, one_smul]
    calc _ = φ (ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * (φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) *
        φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸))) * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)) := by noncomm_ring
      _ = 1 := by rw [hνiν, mul_one, hμiμ]
  have hdetk₁ : Valued.v (tMi q hq * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸))).det = 1 := by
    refine valued_det_eq_one q hq hk₁ hk₁i ?_
    calc tMi q hq * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)) * (φ (ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * tM q hq)
        = tMi q hq * (φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) * tM q hq := by
          noncomm_ring
      _ = 1 := by rw [hμμi, mul_one, tMi_mul_tM]
  have hdetG : Valued.v (((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
      (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((m' : (ℍ𝔸)ˣ) : ℍ𝔸)))).det = 1 := by
    rw [hG_eq, Matrix.det_mul, map_mul, det_gM, valued_det_eq_one q hq hk₀' hk₀i' hkk, one_mul, hdetk₁]
  have hGi : ((q : ℕ) : v.adicCompletion ℚ) •
      (φ (ev v ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) ∈ intMat q hq :=
    inv_mem_intMat_of_valued_det q hq hG hGGi hGiG hdetG

  have hH_eq : ((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
      (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸))) = gM q hq k₀ * k₀ := by
    rw [hν', gM_mul, mul_assoc]
  have hH : ((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
      (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸))) ∈ intMat q hq := by
    rw [hH_eq]; exact (intMat q hq).mul_mem hg hk₀'
  have hHHi : (((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
      (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)))) *
      (((q : ℕ) : v.adicCompletion ℚ) •
        (φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)))) = 1 := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hq0, one_smul]
    calc _ = φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) *
        φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by noncomm_ring
      _ = 1 := by rw [hννi, mul_one, hννi]
  have hHiH : (((q : ℕ) : v.adicCompletion ℚ) •
        (φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)))) *
      (((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
        (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)))) = 1 := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hq0, one_smul]
    calc _ = φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * (φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) *
        φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸))) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) := by noncomm_ring
      _ = 1 := by rw [hνiν, mul_one, hνiν]
  have hdetH : Valued.v (((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
      (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)))).det = 1 := by
    rw [hH_eq, Matrix.det_mul, map_mul, det_gM, valued_det_eq_one q hq hk₀' hk₀i' hkk, one_mul]
  have hHi : ((q : ℕ) : v.adicCompletion ℚ) •
      (φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) ∈ intMat q hq :=
    inv_mem_intMat_of_valued_det q hq hH hHHi hHiH hdetH

  refine ⟨hn_away, hRΛ_v, ?_, ?_, ?_, ?_, hL0, ?_, ?_⟩
  · rw [hφΛ, map_mul, hνi', mul_assoc]
    exact (intMat q hq).mul_mem hk₀i' hk₁
  · rw [hφΛ, map_mul, hν', ← mul_assoc]
    exact (intMat q hq).mul_mem hk₁i hk₀'
  · rw [hφΛ, hφc, map_mul]; exact hG
  · rw [hφΛ, hφc, map_mul]; exact hGi
  · rw [hφΛ, hφc, map_mul]; exact hH
  · rw [hφΛ, hφc, map_mul]; exact hHi

theorem main (q' : ℕ) (hq' : q'.Prime) (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (ℍ𝔸)ˣ) (hm : QuaternionAlgebra.IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m))
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : R = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m)
    (hRN : R.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N) (hq'q : ¬ q' ∣ N * q)
    (m' : (ℍ𝔸)ˣ)
    (hm'₁ : ((m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm'N : ((N * q : ℕ) : ℚ) • ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁)
    (S : Submodule ℤ ℍ[ℚ, a, b]) (hS : S = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m')
    (n : (ℍ𝔸)ˣ) (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    (hSn : S = CerednikDrinfeld.meetOrder R n) (hnorm : Submodule.conjByFiniteIdele S n = S) :
    ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((q : ℕ) : ℚ) • ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((n⁻¹ * m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((N : ℕ) : ℚ) • ((m'⁻¹ * n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((q : ℕ) : ℚ)⁻¹ • ((n * m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((q : ℕ) : ℚ) • (((n * n)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((q : ℕ) : ℚ)⁻¹ • ((n * n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((m'⁻¹ * n * m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((q : ℕ) : ℚ) • ((m'⁻¹ * n⁻¹ * m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ := by
  classical
  obtain ⟨hn_away, hRΛ_v, hL1, hL2, hL3, hL4, hL0, hL5, hL6⟩ :=
    local_facts q' hq' hdef Λ₁ hΛ₁ N m hm R hR hRN q hq hqN hq'q m' hm'₁ hm'N S hS n hn hSn hnorm
  set v : HeightOneSpectrum (𝓞 ℚ) := place q hq with hv
  have hΛo : QuaternionAlgebra.IsOrder Λ₁ := hΛ₁.1
  have hRo : QuaternionAlgebra.IsOrder R := by rw [hR]; exact hΛo.inf hm.1
  have hRΛ₁ : R ≤ Λ₁ := by rw [hR]; exact inf_le_left
  have hSΛ' : S ≤ Submodule.conjByFiniteIdele Λ₁ m' := by rw [hS]; exact inf_le_right
  have hmulΛ : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ),
      x ∈ Submodule.localBox Λ₁ w → y ∈ Submodule.localBox Λ₁ w → x * y ∈ Submodule.localBox Λ₁ w :=
    fun w x y hx hy => mul_mem_localBox Λ₁ w (fun _ _ h1 h2 => hΛo.mul_mem h1 h2) hx hy
  obtain ⟨hn1, hn2, hn3, hn4⟩ := hn

  have hboxS : Submodule.finiteAdeleBox S = Submodule.finiteAdeleBox R ⊓
      (Submodule.finiteAdeleBox R).map
        ((AddMonoidHom.mulRight ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)).comp (AddMonoidHom.mulLeft ((n : (ℍ𝔸)ˣ) : ℍ𝔸))) := by
    rw [hSn]
    exact (QuaternionAlgebra.IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le R hRo n).1
  have hnS : ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox S := by
    rw [hboxS]
    refine ⟨hn1, ⟨_, hn1, ?_⟩⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    rw [Units.mul_inv_cancel_right]
  have hqniS : ((q : ℕ) : ℚ) • ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox S := by
    rw [hboxS]
    refine ⟨hn2, ⟨_, hn2, ?_⟩⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    rw [mul_smul_comm, smul_mul_assoc, Units.mul_inv, one_mul]
  have hboxΛ' := Submodule.finiteAdeleBox_conjByFiniteIdele Λ₁ hΛo.fg hΛo.spanTop m'
  have h8 : ((m'⁻¹ * n * m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ := by
    have := finiteAdeleBox_mono hSΛ' hnS
    rw [hboxΛ', AddSubgroup.mem_map] at this
    obtain ⟨y, hy, hyn⟩ := this
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight] at hyn
    have e : ((m'⁻¹ * n * m' : (ℍ𝔸)ˣ) : ℍ𝔸) = y := by
      rw [Units.val_mul, Units.val_mul, ← hyn]
      calc _ = (((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (m' : ℍ𝔸)) * y * (((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (m' : ℍ𝔸)) := by
            noncomm_ring
        _ = y := by rw [Units.inv_mul, one_mul, mul_one]
    rw [e]; exact hy
  have h9 : ((q : ℕ) : ℚ) • ((m'⁻¹ * n⁻¹ * m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ := by
    have := finiteAdeleBox_mono hSΛ' hqniS
    rw [hboxΛ', AddSubgroup.mem_map] at this
    obtain ⟨y, hy, hyn⟩ := this
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight] at hyn
    have e : ((q : ℕ) : ℚ) • ((m'⁻¹ * n⁻¹ * m' : (ℍ𝔸)ˣ) : ℍ𝔸) = y := by
      rw [Units.val_mul, Units.val_mul, mul_assoc, ← mul_smul_comm, ← smul_mul_assoc, ← hyn]
      calc _ = (((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (m' : ℍ𝔸)) * y * (((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (m' : ℍ𝔸)) := by
            noncomm_ring
        _ = y := by rw [Units.inv_mul, one_mul, mul_one]
    rw [e]; exact hy

  have hm'w : ∀ w, ev w ((m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox Λ₁ w :=
    (mem_finiteAdeleBox_iff Λ₁ hΛo.fg hΛo.spanTop _).1 hm'₁
  have hNm'iw : ∀ w, w ≠ v →
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((N : ℕ) : w.adicCompletion ℚ)) * ev w ((m'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈
        Submodule.localBox Λ₁ w := by
    intro w hw
    have h1 := (mem_finiteAdeleBox_iff Λ₁ hΛo.fg hΛo.spanTop _).1 hm'N w
    rw [ev_smul, algebraMap_natCast] at h1
    have h2 := one_tmul_mul_mem_localBox Λ₁ w h1 (inv_q_mem_integers_of_ne q hq w hw)
    rw [← mul_assoc, one_tmul_mul_one_tmul] at h2
    convert h2 using 3
    all_goals try rfl
    push_cast
    rw [mul_comm ((N : ℕ) : w.adicCompletion ℚ), ← mul_assoc,
      inv_mul_cancel₀ (natCast_ne_zero_of_valuation w q (valuation_q_eq_one_of_ne q hq w hw)), one_mul]
  have hnbox : ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ := finiteAdeleBox_mono hRΛ₁ hn1
  have hnw : ∀ w, ev w ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox Λ₁ w :=
    (mem_finiteAdeleBox_iff Λ₁ hΛo.fg hΛo.spanTop _).1 hnbox
  have hniw : ∀ w, w ≠ v → ev w ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox Λ₁ w :=
    fun w hw => localBox_mono w hRΛ₁ (hn_away w hw).2

  have hC2 : ((n⁻¹ * m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ := by
    rw [mem_finiteAdeleBox_iff Λ₁ hΛo.fg hΛo.spanTop]
    intro w
    rw [Units.val_mul, map_mul]
    by_cases hw : w = v
    · subst hw; exact hL1
    · exact hmulΛ w _ _ (hniw w hw) (hm'w w)

  have hC3 : ((N : ℕ) : ℚ) • ((m'⁻¹ * n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ := by
    rw [mem_finiteAdeleBox_iff Λ₁ hΛo.fg hΛo.spanTop]
    intro w
    rw [ev_smul, algebraMap_natCast, Units.val_mul, map_mul]
    by_cases hw : w = v
    · subst hw; exact one_tmul_mul_mem_localBox Λ₁ _ hL2 (natCast_mem_integers _ N)
    · rw [← mul_assoc]; exact hmulΛ w _ _ (hNm'iw w hw) (hnw w)

  have hC5 : ((q : ℕ) : ℚ)⁻¹ • ((n * m' : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ := by
    rw [mem_finiteAdeleBox_iff Λ₁ hΛo.fg hΛo.spanTop]
    intro w
    rw [ev_smul, map_inv₀, algebraMap_natCast, Units.val_mul, map_mul]
    by_cases hw : w = v
    · subst hw; exact hL3
    · exact one_tmul_mul_mem_localBox Λ₁ w (hmulΛ w _ _ (hnw w) (hm'w w)) (inv_q_mem_integers_of_ne q hq w hw)

  have hC6 : ((q : ℕ) : ℚ) • (((n * n)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ := by
    rw [mem_finiteAdeleBox_iff Λ₁ hΛo.fg hΛo.spanTop]
    intro w
    rw [ev_smul, algebraMap_natCast, mul_inv_rev, Units.val_mul, map_mul]
    by_cases hw : w = v
    · subst hw; exact hL6
    · exact one_tmul_mul_mem_localBox Λ₁ w (hmulΛ w _ _ (hniw w hw) (hniw w hw)) (natCast_mem_integers w q)

  have hC7 : ((q : ℕ) : ℚ)⁻¹ • ((n * n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ₁ := by
    rw [mem_finiteAdeleBox_iff Λ₁ hΛo.fg hΛo.spanTop]
    intro w
    rw [ev_smul, map_inv₀, algebraMap_natCast, Units.val_mul, map_mul]
    by_cases hw : w = v
    · subst hw; exact hL5
    · exact one_tmul_mul_mem_localBox Λ₁ w (hmulΛ w _ _ (hnw w) (hnw w)) (inv_q_mem_integers_of_ne q hq w hw)
  exact ⟨hnbox, finiteAdeleBox_mono hRΛ₁ hn2, hC2, hC3, hC5, hC6, hC7, h8, h9⟩

end Frame

end ALPin

end

open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld

theorem solution
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m))
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : R = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m)
    (hRN : R.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (q : ℕ) [NeZero q] [Fact q.Prime] (hqN : ¬ q ∣ N) (hq'q : ¬ q' ∣ N * q)
    (m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm'₁ : ((m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm'N : ((N * q : ℕ) : ℚ) • ((m'⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm' : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m'))
    (S : Submodule ℤ ℍ[ℚ, a, b]) (hS : S = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m')
    (hSlvl : S.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N * q)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)
    (hSn : S = meetOrder R n) (hnorm : Submodule.conjByFiniteIdele S n = S) :
    ((n : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((q : ℕ) : ℚ) • ((n⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((n⁻¹ * m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((N : ℕ) : ℚ) • ((m'⁻¹ * n : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((q : ℕ) : ℚ)⁻¹ • ((n * m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((q : ℕ) : ℚ) • (((n * n)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((q : ℕ) : ℚ)⁻¹ • ((n * n : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((m'⁻¹ * n * m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ ∧
    ((q : ℕ) : ℚ) • ((m'⁻¹ * n⁻¹ * m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ :=
  ALPin.main q' Fact.out hdef Λ₁ hΛ₁ N m hm R hR hRN q Fact.out hqN hq'q m' hm'₁ hm'N S hS n hn hSn hnorm

end S_QuaternionAlgebra_inv_mul_mem_finiteAdeleBox_and_smul_mul_mem_of_mem_primeHeckeSet_of_conjByFiniteIdele_meetOrder_eq
end P2MW
export P2MW.S_QuaternionAlgebra_inv_mul_mem_finiteAdeleBox_and_smul_mul_mem_of_mem_primeHeckeSet_of_conjByFiniteIdele_meetOrder_eq (solution)
