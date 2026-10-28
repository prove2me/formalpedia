-- Prove2me | solution 1 for OAI.binary_sweep_contraction_and_mixing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T16:05:11.938986+00:00
-- url     : https://prove2.me/submissions/97e824e3-35d0-4f89-86c0-5ba7fd7a487f

import Mathlib
import Definitions.Def_BinarySweep
import Definitions.Def_OAIB3Bs000
import Theorems.Thm_OAI_BinaryCoordinateSweeps_constant_sweep_mixing
import Theorems.Thm_OAI_BinaryCoordinateSweeps_real_grid_bound

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_Basic
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

section FiniteProbability
variable {Ω G : Type*} [Fintype Ω] [Fintype G]

lemma finiteLaw_nonneg (f : Ω → G) (g : G) : 0 ≤ finiteLaw f g := by
  classical
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

lemma finiteLaw_sum [Nonempty Ω] (f : Ω → G) : ∑ g, finiteLaw f g = 1 := by
  classical
  simp only [finiteLaw]
  rw [Finset.sum_comm]
  simp [Fintype.card_ne_zero]

lemma uniformLaw_sum [Nonempty G] : ∑ g, uniformLaw G g = 1 := by
  simp [uniformLaw, Fintype.card_ne_zero]

end FiniteProbability

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_SupportTimeBoundBounds
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma sign_boolSwitch (c : Bool) :
    Equiv.Perm.sign (boolSwitch c) = if c then (-1 : ℤˣ) else 1 := by
  cases c
  · have : boolSwitch false = 1 := by ext x; cases x <;> rfl
    rw [this]; rfl
  · have : boolSwitch true = Equiv.swap false true := by
      ext x; cases x <;> simp [boolSwitch]
    rw [this, Equiv.Perm.sign_swap (by decide)]; rfl

lemma realSign_coordinateLayer (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i ≠ j} → Bool) → Bool) :
    realSign (coordinateLayer d j c) = ∏ y, (if c y then (-1 : ℝ) else 1) := by
  classical
  have he : coordinateLayer d j c =
      (Equiv.piSplitAt j (fun _ : Fin d => Bool)).trans
        ((Equiv.prodCongrLeft (fun y => boolSwitch (c y))).trans
          (Equiv.piSplitAt j (fun _ : Fin d => Bool)).symm) := rfl
  rw [he]
  simp [realSign, Equiv.Perm.sign_prodCongrLeft, sign_boolSwitch, apply_ite]

lemma sum_realSign_coordinateLayer (d : ℕ) (j : Fin d) :
    ∑ c : ({i : Fin d // i ≠ j} → Bool) → Bool,
      realSign (coordinateLayer d j c) = 0 := by
  classical
  simp_rw [realSign_coordinateLayer]
  rw [← Fintype.prod_sum (fun (_ : {i : Fin d // i ≠ j} → Bool) (b : Bool) =>
    if b then (-1 : ℝ) else 1)]
  simp

lemma realSign_binarySweep (d : ℕ) (c : SweepCoins d) :
    realSign (binarySweep d c) = ∏ j, realSign (coordinateLayer d j (c j)) := by
  classical
  simp [binarySweep, map_list_prod, List.map_reverse, List.prod_reverse,
    List.map_ofFn, List.prod_ofFn]

lemma sum_realSign_binarySweep (d : ℕ) (hd : 0 < d) :
    ∑ c : SweepCoins d, realSign (binarySweep d c) = 0 := by
  classical
  simp_rw [realSign_binarySweep]
  rw [← Fintype.prod_sum (fun (j : Fin d) (c : ({i : Fin d // i ≠ j} → Bool) → Bool) =>
    realSign (coordinateLayer d j c))]
  apply Finset.prod_eq_zero (i := ⟨0, hd⟩) (Finset.mem_univ _)
  exact sum_realSign_coordinateLayer d ⟨0, hd⟩

lemma finiteLaw_expectation {Ω G : Type*} [Fintype Ω] [Fintype G]
    (f : Ω → G) (a : G → ℝ) :
    ∑ g, finiteLaw f g * a g = (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, a (f ω) := by
  classical
  simp only [finiteLaw, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul, Finset.mul_sum]

theorem binary_sign_annihilated (d : ℕ) (hd : 0 < d) :
    ∑ g : Equiv.Perm (Slot d), binaryLaw d g * realSign g = 0 := by
  rw [binaryLaw, finiteLaw_expectation, sum_realSign_binarySweep d hd, mul_zero]

lemma coordinateLayer_zero (d : ℕ) (j : Fin d) :
    coordinateLayer d j (fun _ => false) = 1 := by
  ext x i
  simp [coordinateLayer, Equiv.piSplitAt_symm_apply]
  intro h
  rw [h]

lemma prod_reverse_ofFn_single {G : Type*} [Monoid G] (n : ℕ) (j : Fin n) (g : G) :
    (List.ofFn (fun i : Fin n => if i = j then g else 1)).reverse.prod = g := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [List.ofFn_succ, List.ofFn_const]
    · simpa [List.ofFn_succ, (Fin.succ_ne_zero j).symm] using ih j

lemma binarySweep_zero (d : ℕ) : binarySweep d (fun _ _ => false) = 1 := by
  simp [binarySweep, coordinateLayer_zero, List.ofFn_const]

lemma binarySweep_singleLayer (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i ≠ j} → Bool) → Bool) :
    binarySweep d (Function.update ((fun _ _ => false) : SweepCoins d) j c) = coordinateLayer d j c := by
  classical
  have h (i : Fin d) :
      coordinateLayer d i ((Function.update ((fun _ _ => false) : SweepCoins d) j c) i) =
      if i = j then coordinateLayer d j c else 1 := by
    by_cases hi : i = j
    · subst i; simp
    · simp [coordinateLayer_zero, hi]
  simp only [binarySweep, h]
  exact prod_reverse_ofFn_single d j _

lemma coordinateLayer_mem_reachable (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i ≠ j} → Bool) → Bool) :
    coordinateLayer d j c ∈ sweepReachable d := by
  refine ⟨[Function.update ((fun _ _ => false) : SweepCoins d) j c], ?_⟩
  simp [binarySweep_singleLayer]

lemma fiber_boolSwitch_eq_swap {Y : Type*} [DecidableEq Y] (y : Y) (a : Bool) :
    Equiv.prodCongrLeft (fun z => boolSwitch (decide (z = y))) =
      Equiv.swap (a, y) (!a, y) := by
  ext ⟨b, z⟩ <;> cases a <;> cases b <;> by_cases h : z = y <;>
    simp [boolSwitch, Equiv.swap_apply_def, h]

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_CoordinateLayerEdgeSwap
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma coordinateLayer_edgeSwap (d : ℕ) (j : Fin d) (x : Slot d) :
    coordinateLayer d j (fun y => decide (y = fun i : {i : Fin d // i ≠ j} => x i)) =
      Equiv.swap x (Function.update x j (!x j)) := by
  classical
  let e := Equiv.piSplitAt j (fun _ : Fin d => Bool)
  let z : {i : Fin d // i ≠ j} → Bool := fun i => x i
  change (e.trans (Equiv.prodCongrLeft (fun y => boolSwitch (decide (y = z))))).trans e.symm = _
  rw [fiber_boolSwitch_eq_swap z (x j), Equiv.trans_swap_trans_symm]
  have hx : e.symm (x j, z) = x := by
    exact e.symm_apply_apply x
  have hy : e.symm (!x j, z) = Function.update x j (!x j) := by
    ext i
    by_cases h : i = j
    · subst i; simp [e, Equiv.piSplitAt_symm_apply]
    · simp [e, z, Equiv.piSplitAt_symm_apply, h]
  rw [hx, hy]

lemma swap_update_mem_reachable (d : ℕ) (j : Fin d) (x : Slot d) (b : Bool) :
    Equiv.swap x (Function.update x j b) ∈ sweepReachable d := by
  classical
  by_cases h : b = x j
  · subst b
    simp only [Function.update_eq_self, Equiv.swap_self]
    exact (sweepReachable d).one_mem
  · have hb : b = !x j := by cases b <;> cases hx : x j <;> simp_all
    rw [hb, ← coordinateLayer_edgeSwap]
    exact coordinateLayer_mem_reachable d j _

lemma swap_mem_sweepReachable (d : ℕ) (x y : Slot d) :
    Equiv.swap x y ∈ sweepReachable d := by
  classical
  have h (s : Finset (Fin d)) :
      Equiv.swap x (fun i => if i ∈ s then y i else x i) ∈ sweepReachable d := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, ite_false, Equiv.swap_self]
      exact (sweepReachable d).one_mem
    | @insert j s hj ih =>
      have he : (fun i => if i ∈ insert j s then y i else x i) =
          Function.update (fun i => if i ∈ s then y i else x i) j (y j) := by
        ext i
        by_cases hi : i = j
        · subst i; simp
        · simp [hi]
      rw [he]
      exact SubmonoidClass.swap_mem_trans (sweepReachable d) ih
        (swap_update_mem_reachable d j _ _)
  simpa using h Finset.univ

theorem every_permutation_sweepReachable (d : ℕ) (g : Equiv.Perm (Slot d)) :
    g ∈ sweepReachable d := by
  classical
  induction g using Equiv.Perm.swap_induction_on with
  | one => exact (sweepReachable d).one_mem
  | swap_mul g x y h ih =>
    exact (sweepReachable d).mul_mem (swap_mem_sweepReachable d x y) ih

section FiniteRandomWalk
variable {G : Type*} [Fintype G] [Group G]

lemma sum_mulLeft (a : G) (f : G → ℝ) : ∑ g, f (a * g) = ∑ g, f g :=
  Equiv.sum_comp (Equiv.mulLeft a) f

lemma sum_inv_mulRight (a : G) (f : G → ℝ) : ∑ g, f (g⁻¹ * a) = ∑ g, f g :=
  ((Equiv.inv G).trans (Equiv.mulRight a)).sum_comp f

lemma convolution_sum (p q : G → ℝ) :
    ∑ g, convolution p q g = (∑ g, p g) * (∑ g, q g) := by
  simp only [convolution]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_mulLeft]
  rw [Finset.sum_mul]

lemma convolution_nonneg {p q : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hq : ∀ g, 0 ≤ q g) :
    ∀ g, 0 ≤ convolution p q g := fun _ =>
  Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (hq _))

lemma convolution_probability {p q : G → ℝ} (hp : IsProbability p) (hq : IsProbability q) :
    IsProbability (convolution p q) := by
  exact ⟨convolution_nonneg hp.1 hq.1, by rw [convolution_sum, hp.2, hq.2, one_mul]⟩

lemma convolution_uniform_right {p : G → ℝ} (hp : ∑ g, p g = 1) :
    convolution p (uniformLaw G) = uniformLaw G := by
  funext g
  simp [convolution, uniformLaw, ← Finset.sum_mul, hp]

lemma convolution_uniform_left {p : G → ℝ} (hp : ∑ g, p g = 1) :
    convolution (uniformLaw G) p = uniformLaw G := by
  funext g
  simp [convolution, uniformLaw, ← Finset.mul_sum, sum_inv_mulRight, hp]

lemma convolution_assoc (p q r : G → ℝ) :
    convolution (convolution p q) r = convolution p (convolution q r) := by
  funext g
  simp only [convolution, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← sum_mulLeft x (fun y => p x * q (x⁻¹ * y) * r (y⁻¹ * g))]
  simp [mul_assoc]

omit [Group G] in
lemma totalVariation_nonneg (p q : G → ℝ) : 0 ≤ totalVariation p q :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

omit [Group G] in
lemma totalVariation_le_one {p q : G → ℝ} (hp : IsProbability p) (hq : IsProbability q) :
    totalVariation p q ≤ 1 := by
  have h : ∑ g, |p g - q g| ≤ 2 := by
    calc
      _ ≤ ∑ g, (p g + q g) := Finset.sum_le_sum (fun g _ =>
        (abs_sub (p g) (q g)).trans_eq (by rw [abs_of_nonneg (hp.1 g), abs_of_nonneg (hq.1 g)]))
      _ = 2 := by rw [Finset.sum_add_distrib, hp.2, hq.2]; norm_num
  unfold totalVariation
  linarith

lemma convolution_tv_contract {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (q r : G → ℝ) :
    totalVariation (convolution p q) (convolution p r) ≤
      (∑ g, p g) * totalVariation q r := by
  have h : ∑ g, |convolution p q g - convolution p r g| ≤
      (∑ g, p g) * ∑ g, |q g - r g| := by
    calc
      _ = ∑ g, |∑ x, p x * (q (x⁻¹ * g) - r (x⁻¹ * g))| := by
        simp_rw [convolution, ← Finset.sum_sub_distrib, ← mul_sub]
      _ ≤ ∑ g, ∑ x, p x * |q (x⁻¹ * g) - r (x⁻¹ * g)| := by
        apply Finset.sum_le_sum
        intro g _
        simpa only [abs_mul, abs_of_nonneg (hp _)] using
          (Finset.abs_sum_le_sum_abs (s := Finset.univ)
            (f := fun x => p x * (q (x⁻¹ * g) - r (x⁻¹ * g))))
      _ = _ := by
        rw [Finset.sum_comm]
        have hs (x : G) : ∑ g, |q (x⁻¹ * g) - r (x⁻¹ * g)| = ∑ g, |q g - r g| :=
          sum_mulLeft x⁻¹ (fun g => |q g - r g|)
        simp_rw [← Finset.mul_sum, hs]
        rw [Finset.sum_mul]
  unfold totalVariation
  nlinarith

end FiniteRandomWalk

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_FiniteUnitaryAverage
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma complexAverage_apply (ρ : Representation ℂ G V) (p : G → ℂ) (v : V) :
    complexAverage ρ p v = ∑ g, p g • ρ g v := by
  simp [complexAverage,Irrep.groupAverage]

lemma complexAverage_norm_apply (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) (p : G → ℂ) (v : V) :
    ‖complexAverage ρ p v‖ ≤ (∑g, ‖p g‖)*‖v‖ := by
  rw [complexAverage_apply,Finset.sum_mul]
  exact (norm_sum_le _ _).trans_eq (by simp [norm_smul,hρ])

lemma realAverage_contraction (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) {p : G → ℝ} (hp : IsProbability p) (v : V) :
    ‖complexAverage ρ (fun g => (p g:ℂ)) v‖ ≤ ‖v‖ := by
  have he : (∑g, ‖(p g:ℂ)‖)=1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp.1 _)] using hp.2
  simpa only [he,one_mul] using complexAverage_norm_apply ρ hρ (fun g => (p g:ℂ)) v

lemma complexAverage_sub (ρ : Representation ℂ G V) (p q : G → ℂ) :
    complexAverage ρ (fun g => p g-q g)=complexAverage ρ p-complexAverage ρ q := by
  ext v
  simp [complexAverage_apply,sub_smul,Finset.sum_sub_distrib]

lemma complexAverage_convolution (ρ : Representation ℂ G V) (p q : G → ℝ) :
    complexAverage ρ (fun g => (convolution p q g:ℂ)) =
      complexAverage ρ (fun g => (p g:ℂ))*complexAverage ρ (fun g => (q g:ℂ)) := by
  ext v
  calc
    _ = ∑ x, ∑ y, (p x:ℂ) • (q y:ℂ) • ρ (x*y) v := by
      rw [complexAverage_apply]
      simp only [convolution,Complex.ofReal_sum,Finset.sum_smul,
        Complex.ofReal_mul,mul_smul]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simpa only [Equiv.coe_mulLeft,inv_mul_cancel_left] using
        (Equiv.sum_comp (Equiv.mulLeft x)
          (fun y => (p x:ℂ) • (q (x⁻¹*y):ℂ) • ρ y v)).symm
    _ = _ := by
      rw [mul_apply_eq_comp,complexAverage_apply]
      apply Finset.sum_congr rfl
      intro x _
      rw [complexAverage_apply,map_sum,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [map_smul,map_mul,Module.End.mul_apply]

lemma complexAverage_pointMass (ρ : Representation ℂ G V) :
    complexAverage ρ (fun g => (pointMassOne g:ℂ))=1 := by
  ext v
  simp [complexAverage_apply,pointMassOne]

lemma complexAverage_power (ρ : Representation ℂ G V) (p : G → ℝ) (n : ℕ) :
    complexAverage ρ (fun g => (convolutionPower p n g:ℂ))=
      (complexAverage ρ (fun g => (p g:ℂ)))^n := by
  induction n with
  | zero => exact complexAverage_pointMass ρ
  | succ n ih => rw [convolutionPower,complexAverage_convolution,ih,pow_succ']

lemma complexAverage_uniform_left (ρ : Representation ℂ G V) (g : G) (v : V) :
    ρ g (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v)=
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v := by
  simp only [complexAverage_apply,map_sum,map_smul,←Module.End.mul_apply,←map_mul,uniformLaw]
  simpa only [Equiv.coe_mulLeft,Complex.ofReal_inv] using
    Equiv.sum_comp (Equiv.mulLeft g) (fun x => ((Fintype.card G:ℝ)⁻¹:ℂ) • ρ x v)

lemma complexAverage_uniform_right (ρ : Representation ℂ G V) (g : G) (v : V) :
    complexAverage ρ (fun g => (uniformLaw G g:ℂ)) (ρ g v)=
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v := by
  simp only [complexAverage_apply,←Module.End.mul_apply,←map_mul,uniformLaw]
  simpa only [Equiv.coe_mulRight,Complex.ofReal_inv] using
    Equiv.sum_comp (Equiv.mulRight g) (fun x => ((Fintype.card G:ℝ)⁻¹:ℂ) • ρ x v)

lemma complexAverage_uniform_idem (ρ : Representation ℂ G V) (v : V) :
    complexAverage ρ (fun g => (uniformLaw G g:ℂ))
      (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v) =
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v := by
  rw [complexAverage_apply]
  simp only [complexAverage_uniform_left,←Finset.sum_smul,←Complex.ofReal_sum,uniformLaw_sum,
    Complex.ofReal_one,one_smul]

lemma complexAverage_uniform_inner (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) (v w : V) :
    inner ℂ (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v) w =
      inner ℂ v (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) w) := by
  simp only [complexAverage_apply,inner_sum,inner_smul_left, sum_inner,
    inner_smul_right,Complex.conj_ofReal]
  have he (g : G) : inner ℂ (ρ g v) w=inner ℂ v (ρ g⁻¹ w) := by
    rw [←LinearMap.adjoint_inner_right,Irrep.unitary_rep_adjoint ρ hρ]
  simp_rw [he]
  simpa only [uniformLaw,Equiv.inv_apply,Complex.ofReal_inv] using
    Equiv.sum_comp (Equiv.inv G) (fun g => ((Fintype.card G:ℝ)⁻¹:ℂ)*inner ℂ v (ρ g w))

lemma complexAverage_variance (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) {p : G → ℝ} (hp : IsProbability p) (v : V) :
    ∑g, p g * ‖ρ g v-complexAverage ρ (fun g => (p g:ℂ)) v‖^2 =
      ‖v‖^2-‖complexAverage ρ (fun g => (p g:ℂ)) v‖^2 := by
  let B := complexAverage ρ (fun g => (p g:ℂ))
  have hi : ∑g, p g * (inner ℂ (ρ g v) (B v)).re=‖B v‖^2 := by
    have he : ∑g, (p g:ℂ)*inner ℂ (ρ g v) (B v)=inner ℂ (B v) (B v) := by
      rw [show B v=∑g, (p g:ℂ) • ρ g v from complexAverage_apply ρ _ v]
      rw [sum_inner]
      simp only [inner_smul_left,Complex.conj_ofReal]
    have hre := congrArg Complex.re he
    have hsq : (inner ℂ (B v) (B v)).re=‖B v‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) (B v)
    rw [hsq] at hre
    simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,inner_self_eq_norm_sq] using hre
  simp only [@norm_sub_sq ℂ V _ _,hρ,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [←Finset.sum_mul,hp.2,one_mul,←Finset.sum_mul,hp.2,one_mul]
  have hs : (∑g, p g*(2*(inner ℂ (ρ g v) (B v)).re))=2*‖B v‖^2 := by
    rw [←hi,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  change ‖v‖^2-(∑g, p g*(2*(inner ℂ (ρ g v) (B v)).re))+‖B v‖^2=_
  rw [hs]
  ring

lemma realAverage_identity_defect (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) {p : G → ℝ} (hp : IsProbability p) (v : V) :
    p 1*‖v-complexAverage ρ (fun g => (p g:ℂ)) v‖^2 ≤
      ‖v‖^2-‖complexAverage ρ (fun g => (p g:ℂ)) v‖^2 := by
  rw [←complexAverage_variance ρ hρ hp]
  simpa only [map_one,Module.End.one_apply] using Finset.single_le_sum (fun g _ => mul_nonneg (hp.1 g)
    (sq_nonneg ‖ρ g v-complexAverage ρ (fun g => (p g:ℂ)) v‖))
    (Finset.mem_univ (1:G))

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_IndependentOperator
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma independent_reverse_product {R : Type*} [Semiring R] {n : ℕ}
    {X : Fin n → Type*} [∀j, Fintype (X j)] (A : (j : Fin n) → X j → R) :
    (List.ofFn (fun j => ∑a, A j a)).reverse.prod=
      ∑f : ∀j, X j, (List.ofFn (fun j => A j (f j))).reverse.prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.reverse_cons,List.prod_append,List.prod_singleton,ih]
    rw [←Equiv.sum_comp (Fin.consEquiv X),Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro f _
    simp only [Fin.consEquiv,Equiv.coe_fn_mk,List.ofFn_succ,List.reverse_cons,
      List.prod_append,List.prod_singleton,Fin.cons_zero,Fin.cons_succ]

lemma weighted_reverse_product {R : Type*} [Semiring R] [Algebra ℂ R] {n : ℕ}
    (w : Fin n → ℂ) (A : Fin n → R) :
    (List.ofFn (fun j => w j • A j)).reverse.prod=
      (∏j,w j) • (List.ofFn A).reverse.prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.reverse_cons,List.prod_append,List.prod_singleton,
      Fin.prod_univ_succ]
    rw [ih,smul_mul_smul_comm,mul_comm (∏j : Fin n, w j.succ) (w 0)]

lemma independent_average_product {R : Type*} [Semiring R] [Algebra ℂ R] {n : ℕ}
    {X : Fin n → Type*} [∀j, Fintype (X j)]
    (w : (j : Fin n) → X j → ℂ) (A : (j : Fin n) → X j → R) :
    (∑f : ∀j, X j, (∏j,w j (f j)) •
      (List.ofFn (fun j => A j (f j))).reverse.prod)=
      (List.ofFn (fun j => ∑a, w j a • A j a)).reverse.prod := by
  rw [independent_reverse_product]
  exact Finset.sum_congr rfl (fun f _ => (weighted_reverse_product _ _).symm)

lemma reverse_product_norm_le_one {R : Type*} [NormedRing R] [NormOneClass R]
    {n : ℕ} (A : Fin n → R) (hA : ∀j, ‖A j‖≤1) :
    ‖(List.ofFn A).reverse.prod‖≤1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.reverse_cons,List.prod_append,List.prod_singleton]
    exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      (ih _ (fun index => hA index.succ))).trans (hA 0))

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma pi_single_reverse {I G : Type*} [Fintype I] [DecidableEq I] [Group G]
    (f : I → G) (e : Fin (Fintype.card I) ≃ I) :
    (List.ofFn (fun j => Pi.mulSingle (e j) (f (e j)))).reverse.prod=f := by
  funext i
  have hh := List.prod_map_eq_pow_single (e.symm i)
    (fun j => (Pi.mulSingle (e j) (f (e j)) : I → G) i)
    (l := (List.ofFn (fun j : Fin (Fintype.card I) => j)).reverse) (by
      intro j hj _
      have hne : i ≠ e j := by
        intro he
        apply hj
        exact e.injective (he.symm.trans (e.apply_symm_apply i).symm)
      simp [Pi.mulSingle,hne])
  have hc : ((List.ofFn (fun j : Fin (Fintype.card I) => j)).reverse).count (e.symm i)=1 := by
    apply List.count_eq_one_of_mem
    · exact List.nodup_reverse.mpr (List.nodup_ofFn.mpr Function.injective_id)
    · simp
  rw [hc,pow_one,e.apply_symm_apply,Pi.mulSingle_eq_same] at hh
  simp only [List.map_reverse,List.map_ofFn,Function.comp_def] at hh
  change (Pi.evalMonoidHom (fun _ : I => G) i)
    ((List.ofFn (fun j => Pi.mulSingle (e j) (f (e j)))).reverse.prod)=f i
  rw [map_list_prod,List.map_reverse,List.map_ofFn]
  exact hh

variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma complexAverage_sum (ρ : Representation ℂ G V) (p : G → ℂ) :
    complexAverage ρ p=∑g,p g • continuousRep ρ g := by
  ext v
  simp [complexAverage_apply,continuousRep]

theorem pi_average_norm_le_one {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq G] [Nontrivial V]
    (ρ : Representation ℂ (I → G) V) (p : I → G → ℂ)
    (h : ∀i, ‖complexAverage (ρ.comp (MonoidHom.mulSingle (fun _ : I => G) i)) (p i)‖≤1) :
    ‖complexAverage ρ (fun f => ∏i,p i (f i))‖≤1 := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let E : (Fin (Fintype.card I) → G) ≃ (I → G) := Equiv.piCongrLeft (fun _ => G) e
  have he (f : Fin (Fintype.card I) → G) : ∀j, E f (e j)=f j := by
    intro j; simp [E,Equiv.piCongrLeft]
  have hf : complexAverage ρ (fun f => ∏i,p i (f i))=
      (List.ofFn (fun j => complexAverage
        (ρ.comp (MonoidHom.mulSingle (fun _ : I => G) (e j))) (p (e j)))).reverse.prod := by
    rw [complexAverage_sum,←Equiv.sum_comp E]
    simp_rw [←e.prod_comp (fun i => p i (E _ i))]
    have ht (f : Fin (Fintype.card I) → G) : continuousRep ρ (E f)=
        (List.ofFn (fun j => continuousRep ρ (Pi.mulSingle (e j) (f j)))).reverse.prod := by
      rw [←pi_single_reverse (E f) e,map_list_prod,List.map_reverse,List.map_ofFn]
      simp only [Function.comp_def,he]
    simp_rw [ht,he]
    rw [independent_average_product (X := fun _ => G)
      (fun j a => p (e j) a) (fun j a => continuousRep ρ (Pi.mulSingle (e j) a))]
    congr 3
    funext j
    rw [complexAverage_sum]
    rfl
  rw [hf]
  exact reverse_product_norm_le_one _ (fun j => h (e j))

lemma pi_comp_average_norm_le_one {I H : Type*} [Fintype I] [DecidableEq I] [DecidableEq G] [Group H] [Fintype H]
    [Nontrivial V] (ρ : Representation ℂ H V) (φ : (I → G) →* H)
    (p : G → ℂ) (hρ : ∀g v, ‖ρ g v‖=‖v‖)
    (hp : ∀σ : Representation ℂ G V, (∀g v, ‖σ g v‖=‖v‖) →
      ‖complexAverage σ p‖≤1) :
    ‖complexAverage (ρ.comp φ) (fun f => ∏i,p (f i))‖≤1 := by
  apply pi_average_norm_le_one
  intro i
  apply hp
  exact fun g v => hρ _ v

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_FiniteAverageGap
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma realAverage_uniform_commute (ρ : Representation ℂ G V) {p : G → ℝ}
    (hp : IsProbability p) (v : V) :
    complexAverage ρ (fun g => (p g:ℂ))
        (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v)=
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v ∧
    complexAverage ρ (fun g => (uniformLaw G g:ℂ))
        (complexAverage ρ (fun g => (p g:ℂ)) v)=
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v := by
  constructor
  · rw [complexAverage_apply]
    simp only [complexAverage_uniform_left,←Finset.sum_smul,←Complex.ofReal_sum,hp.2,
      Complex.ofReal_one,one_smul]
  · rw [complexAverage_apply ρ (fun g => (p g:ℂ)),map_sum]
    simp only [map_smul,complexAverage_uniform_right,←Finset.sum_smul,←Complex.ofReal_sum,
      hp.2,Complex.ofReal_one,one_smul]

lemma realAverage_TV_bound (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) (p q : G → ℝ) (v : V) :
    ‖complexAverage ρ (fun g => (p g:ℂ)) v-
      complexAverage ρ (fun g => (q g:ℂ)) v‖ ≤ 2*totalVariation p q*‖v‖ := by
  have he : ∑g, ‖((p g:ℂ)-(q g:ℂ))‖=2*totalVariation p q := by
    simp only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,totalVariation]
    ring
  simpa only [complexAverage_sub,sub_apply,he] using
    complexAverage_norm_apply ρ hρ (fun g => (p g:ℂ)-(q g:ℂ)) v

omit [FiniteDimensional ℂ V] in
lemma contraction_power_drift (B : V →L[ℂ] V) (hB : ∀v, ‖B v‖ ≤ ‖v‖) (n : ℕ) (v : V) :
    ‖v-(B^n) v‖ ≤ n*‖v-B v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : v-(B^(n+1)) v=(v-B v)+B (v-(B^n) v) := by
      rw [pow_succ',mul_apply_eq_comp,map_sub]
      abel
    rw [he,Nat.cast_add,Nat.cast_one,add_mul]
    calc
      _ ≤ ‖v-B v‖ + ‖B (v-(B^n) v)‖ := norm_add_le _ _
      _ ≤ ‖v-B v‖ + n*‖v-B v‖ := by linarith [hB (v-(B^n) v)]
      _ = _ := by ring

theorem finite_average_gap (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) {p : G → ℝ} (hp : IsProbability p)
    (hp1 : 0 < p 1) {L : ℕ} (hL : 0<L)
    (hTV : totalVariation (convolutionPower p L) (uniformLaw G) ≤ 1/4)
    (v : V) (hv : complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v=0) :
    ‖complexAverage ρ (fun g => (p g:ℂ)) v‖^2 ≤
      (1-p 1/(4*(L:ℝ)^2))*‖v‖^2 := by
  let B := complexAverage ρ (fun g => (p g:ℂ))
  have hLp : (0:ℝ)<L := by exact_mod_cast hL
  have hpow : ‖(B^L) v‖ ≤ ‖v‖/2 := by
    have ht := realAverage_TV_bound ρ hρ (convolutionPower p L) (uniformLaw G) v
    rw [complexAverage_power,hv,sub_zero] at ht
    calc _ ≤ 2*totalVariation (convolutionPower p L) (uniformLaw G)*‖v‖ := ht
         _ ≤ ‖v‖/2 := by nlinarith [mul_le_mul_of_nonneg_right hTV (norm_nonneg v)]
  have hd := contraction_power_drift B (realAverage_contraction ρ hρ hp) L v
  have hn : ‖v‖ ≤ ‖v-(B^L) v‖+‖(B^L) v‖ := by simpa only [add_comm] using norm_le_insert' v ((B^L) v)
  have hc : ‖v‖/2 ≤ (L:ℝ)*‖v-B v‖ := by linarith
  have hcs : ‖v‖^2 ≤ 4*(L:ℝ)^2*‖v-B v‖^2 := by
    have hs := mul_self_le_mul_self (by positivity : 0≤‖v‖/2) hc
    nlinarith
  have hdef := realAverage_identity_defect ρ hρ hp v
  change p 1*‖v-B v‖^2 ≤ ‖v‖^2-‖B v‖^2 at hdef
  have hscale : p 1/(4*(L:ℝ)^2)*‖v‖^2 ≤ p 1*‖v-B v‖^2 := by
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hcs hp1.le]
  change ‖B v‖^2 ≤ _
  nlinarith

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem finite_average_disk {p : G → ℝ} (hp : IsProbability p)
    (hp1 : 0<p 1) {L : ℕ} (hL : 0<L)
    (hTV : totalVariation (convolutionPower p L) (uniformLaw G) ≤ 1/4) :
    ∃ R : ℝ, 1<R ∧ ∀ (V : Type*) [NormedAddCommGroup V]
      [InnerProductSpace ℂ V] [FiniteDimensional ℂ V], ∀ (ρ : Representation ℂ G V),
      (∀g v, ‖ρ g v‖=‖v‖) → ∀z : ℂ, ‖z‖ ≤ R →
      ‖complexAverage ρ (fun g => (uniformLaw G g:ℂ))+
        z • (complexAverage ρ (fun g => (p g:ℂ))-
          complexAverage ρ (fun g => (uniformLaw G g:ℂ)))‖ ≤ 1 := by
  let c : ℝ := p 1/(4*(L:ℝ)^2)
  have hLp : (0:ℝ)<L := by exact_mod_cast hL
  have hL1 : (1:ℝ)≤L := by exact_mod_cast hL
  have hp1le : p 1≤1 := by
    rw [←hp.2]
    exact Finset.single_le_sum (fun g _ => hp.1 g) (Finset.mem_univ 1)
  have hc : 0<c := by dsimp [c]; positivity
  have hc1 : c≤1 := by
    dsimp [c]
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg ((L:ℝ)-1)]
  let R : ℝ := 1+c/4
  have hR : 1<R := by dsimp [R]; linarith
  have hRq : R^2*(1-c) ≤ 1 := by
    dsimp [R]
    nlinarith [sq_nonneg c,mul_nonneg hc.le (sq_nonneg c)]
  refine ⟨R,hR,?_⟩
  intro V _ _ _ ρ hρ z hz
  let P := complexAverage ρ (fun g => (uniformLaw G g:ℂ))
  let B := complexAverage ρ (fun g => (p g:ℂ))
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [one_mul]
  let u := P v
  let w := v-u
  have hPw : P w=0 := by
    change P (v-P v)=0
    rw [map_sub,complexAverage_uniform_idem,sub_self]
  have hPBw : P (B w)=0 := by
    rw [(realAverage_uniform_commute ρ hp w).2,hPw]
  have hiw : inner ℂ u w=0 := by
    change inner ℂ (P v) w=0
    rw [complexAverage_uniform_inner ρ hρ,hPw,inner_zero_right]
  have hiB : inner ℂ u (B w)=0 := by
    change inner ℂ (P v) (B w)=0
    rw [complexAverage_uniform_inner ρ hρ,hPBw,inner_zero_right]
  have hvsplit : v=u+w := by dsimp [w]; abel
  have hvsq : ‖v‖^2=‖u‖^2+‖w‖^2 := by
    calc ‖v‖^2=‖u+w‖^2 := congrArg (fun x : V => ‖x‖^2) hvsplit
         _ = _ := by simpa only [pow_two] using
           norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u w hiw
  have hB : ‖B w‖^2 ≤ (1-c)*‖w‖^2 := finite_average_gap ρ hρ hp hp1 hL hTV w hPw
  have he : (P+z • (B-P)) v=u+z • B w := by
    simp only [add_apply,smul_apply,sub_apply]
    have hu : B u=u := (realAverage_uniform_commute ρ hp v).1
    have hb : B v=B u+B w := by rw [←map_add,←hvsplit]
    rw [hb,hu,show P v=u from rfl]
    abel_nf
  change ‖(P+z • (B-P)) v‖ ≤ ‖v‖
  rw [he]
  have hs : ‖u+z • B w‖^2=‖u‖^2+‖z‖^2*‖B w‖^2 := by
    have hi : inner ℂ u (z • B w)=0 := by rw [inner_smul_right,hiB,mul_zero]
    have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u (z • B w) hi
    simpa only [←pow_two,norm_smul,mul_pow] using hh
  have hzq : ‖z‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have htot : ‖z‖^2*‖B w‖^2 ≤ ‖w‖^2 := by
    calc _ ≤ R^2*‖B w‖^2 := mul_le_mul_of_nonneg_right hzq (sq_nonneg _)
         _ ≤ R^2*((1-c)*‖w‖^2) := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
         _ ≤ ‖w‖^2 := by nlinarith [mul_le_mul_of_nonneg_right hRq (sq_nonneg ‖w‖)]
  nlinarith [norm_nonneg (u+z • B w),norm_nonneg v]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_GridSweepPath
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

variable {G : Type*} [Fintype G] [Group G]

lemma uniformLaw_probability : IsProbability (uniformLaw G) :=
  ⟨fun _ => by unfold uniformLaw; positivity, uniformLaw_sum⟩

lemma convolution_sub_left (p q r : G → ℝ) :
    convolution (fun g => p g - q g) r = fun g => convolution p r g - convolution q r g := by
  funext g
  simp [convolution, sub_mul, Finset.sum_sub_distrib]

lemma convolution_smul_left (a : ℝ) (p q : G → ℝ) :
    convolution (fun g => a * p g) q = fun g => a * convolution p q g := by
  funext g
  simp [convolution, mul_assoc, Finset.mul_sum]

lemma convolution_uniform_right_mass (p : G → ℝ) :
    convolution p (uniformLaw G) = fun g => (∑ x, p x) * uniformLaw G g := by
  funext g
  simp [convolution, uniformLaw, Finset.sum_mul]

lemma convolution_minorization {p q : G → ℝ} (hp : IsProbability p) (hq : IsProbability q)
    (δ : ℝ) (hδ : ∀ g, δ * uniformLaw G g ≤ p g) :
    totalVariation (convolution p q) (uniformLaw G) ≤
      (1 - δ) * totalVariation q (uniformLaw G) := by
  let r : G → ℝ := fun g => p g - δ * uniformLaw G g
  have hr : ∀ g, 0 ≤ r g := fun g => sub_nonneg.mpr (hδ g)
  have hmass : ∑ g, r g = 1 - δ := by
    simp [r, Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2, uniformLaw_sum]
  have he : totalVariation (convolution p q) (uniformLaw G) =
      totalVariation (convolution r q) (convolution r (uniformLaw G)) := by
    have hdiff (g : G) : convolution r q g - convolution r (uniformLaw G) g =
        convolution p q g - uniformLaw G g := by
      rw [show r = (fun g => p g - δ * uniformLaw G g) from rfl,
        convolution_sub_left, convolution_smul_left, convolution_uniform_left hq.2]
      rw [← show r = (fun g => p g - δ * uniformLaw G g) from rfl,
        convolution_uniform_right_mass, hmass]
      ring
    simp only [totalVariation, hdiff]
  rw [he]
  simpa only [hmass] using convolution_tv_contract hr q (uniformLaw G)

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_PointMassOne
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
section FiniteRandomWalkConvergence
variable {G : Type*} [Fintype G] [Group G]

lemma pointMassOne_probability : IsProbability (pointMassOne : G → ℝ) := by
  classical
  constructor
  · intro g; unfold pointMassOne; split_ifs <;> norm_num
  · simp [pointMassOne]

lemma convolution_one_left (p : G → ℝ) : convolution pointMassOne p = p := by
  classical
  funext g
  simp [convolution, pointMassOne, ite_mul]

lemma convolutionPower_probability {p : G → ℝ} (hp : IsProbability p) (n : ℕ) :
    IsProbability (convolutionPower p n) := by
  induction n with
  | zero => exact pointMassOne_probability
  | succ n ih => exact convolution_probability hp ih

lemma convolutionPower_add (p : G → ℝ) (m n : ℕ) :
    convolutionPower p (m + n) = convolution (convolutionPower p m) (convolutionPower p n) := by
  induction m with
  | zero => simp [convolutionPower, convolution_one_left]
  | succ m ih =>
    simpa only [Nat.succ_add, convolutionPower, ih] using
      (convolution_assoc p (convolutionPower p m) (convolutionPower p n)).symm

lemma convolutionPower_block_bound {p : G → ℝ} (hp : IsProbability p) (L : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ 1 - δ)
    (hδ : ∀ g, δ * uniformLaw G g ≤ convolutionPower p L g) (k : ℕ) :
    totalVariation (convolutionPower p (L * k)) (uniformLaw G) ≤ (1 - δ) ^ k := by
  induction k with
  | zero =>
    simp only [mul_zero, pow_zero]
    exact totalVariation_le_one (convolutionPower_probability hp 0) uniformLaw_probability
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm, convolutionPower_add]
    calc
      _ ≤ (1 - δ) * totalVariation (convolutionPower p (L * k)) (uniformLaw G) :=
        convolution_minorization (convolutionPower_probability hp L)
          (convolutionPower_probability hp (L * k)) δ hδ
      _ ≤ (1 - δ) * (1 - δ) ^ k := mul_le_mul_of_nonneg_left ih hδ0
      _ = _ := by rw [pow_succ]; ring

lemma convolutionPower_all_time_bound {p : G → ℝ} (hp : IsProbability p) (L : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ 1 - δ)
    (hδ : ∀ g, δ * uniformLaw G g ≤ convolutionPower p L g) (t : ℕ) :
    totalVariation (convolutionPower p t) (uniformLaw G) ≤ (1 - δ) ^ (t / L) := by
  have he := convolutionPower_add p (t % L) (L * (t / L))
  rw [Nat.mod_add_div] at he
  rw [he, ← convolution_uniform_right (convolutionPower_probability hp (t % L)).2]
  have hc := convolution_tv_contract (convolutionPower_probability hp (t % L)).1
    (convolutionPower p (L * (t / L))) (uniformLaw G)
  rw [(convolutionPower_probability hp (t % L)).2, one_mul] at hc
  exact hc.trans (convolutionPower_block_bound hp L hδ0 hδ (t / L))

lemma uniformLaw_le_one (g : G) : uniformLaw G g ≤ 1 := by
  have hc : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  exact (inv_le_one₀ (by linarith)).mpr hc

theorem convolutionPower_tendsto_uniform {p : G → ℝ} (hp : IsProbability p)
    {L : ℕ} (hL : 0 < L) (hpos : ∀ g, 0 < convolutionPower p L g) :
    Filter.Tendsto (fun t => totalVariation (convolutionPower p t) (uniformLaw G))
      Filter.atTop (nhds 0) := by
  classical
  let ε := Finset.univ.inf' Finset.univ_nonempty (convolutionPower p L)
  have hε : 0 < ε := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun g _ => hpos g)
  let δ : ℝ := min (1 / 2) ε
  have hδpos : 0 < δ := lt_min (by norm_num) hε
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδ0 : 0 ≤ 1 - δ := by linarith
  have hδ : ∀ g, δ * uniformLaw G g ≤ convolutionPower p L g := by
    intro g
    calc
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (uniformLaw_le_one g) hδpos.le
      _ = δ := mul_one _
      _ ≤ ε := min_le_right _ _
      _ ≤ _ := Finset.inf'_le _ (Finset.mem_univ g)
  apply squeeze_zero (fun _ => totalVariation_nonneg _ _)
    (convolutionPower_all_time_bound hp L hδ0 hδ)
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 (by linarith)).comp
    (Nat.tendsto_div_const_atTop hL.ne')

end FiniteRandomWalkConvergence

lemma finiteLaw_pos_of_mem {Ω G : Type*} [Fintype Ω] [Fintype G]
    (f : Ω → G) (ω : Ω) : 0 < finiteLaw f (f ω) := by
  classical
  have : Nonempty Ω := ⟨ω⟩
  apply Finset.sum_pos'
  · intro a _; split_ifs <;> positivity
  · exact ⟨ω, Finset.mem_univ _, by simp [Fintype.card_pos]⟩

section ReachableRandomWalk
variable {G Ω : Type*} [Fintype G] [Group G] [Fintype Ω] [Nonempty Ω]

lemma convolution_pos_at_mul {p q : G → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    {g h : G} (hg : 0 < p g) (hh : 0 < q h) : 0 < convolution p q (g * h) := by
  classical
  apply Finset.sum_pos'
  · intro x _; exact mul_nonneg (hp x) (hq _)
  · refine ⟨g, Finset.mem_univ _, ?_⟩
    simpa using mul_pos hg hh

lemma convolutionPower_pos_list (f : Ω → G) (l : List Ω) :
    0 < convolutionPower (finiteLaw f) l.length (l.map f).prod := by
  induction l with
  | nil => simp [convolutionPower, pointMassOne]
  | cons a l ih =>
    simpa only [List.length_cons, List.map_cons, List.prod_cons, convolutionPower] using
      convolution_pos_at_mul (finiteLaw_nonneg f)
        (convolutionPower_probability ⟨finiteLaw_nonneg f, finiteLaw_sum f⟩ l.length).1
        (finiteLaw_pos_of_mem f a) ih

lemma convolutionPower_pos_later {p : G → ℝ} (hp : IsProbability p) (h1 : 0 < p 1)
    {g : G} {n m : ℕ} (hn : 0 < convolutionPower p n g) (hnm : n ≤ m) :
    0 < convolutionPower p m g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    change 0 < convolution p (convolutionPower p (n + k)) g
    simpa only [one_mul] using
      convolution_pos_at_mul hp.1 (convolutionPower_probability hp (n + k)).1 h1 ih

lemma finiteLaw_fullSupport_power (f : Ω → G) (ω₀ : Ω) (hω₀ : f ω₀ = 1)
    (hgen : ∀ g : G, ∃ l : List Ω, (l.map f).prod = g) :
    ∃ L : ℕ, 0 < L ∧ ∀ g, 0 < convolutionPower (finiteLaw f) L g := by
  classical
  choose l hl using hgen
  let L := 1 + ∑ g : G, (l g).length
  refine ⟨L, by dsimp [L]; omega, ?_⟩
  intro g
  apply convolutionPower_pos_later ⟨finiteLaw_nonneg f, finiteLaw_sum f⟩
    (hω₀ ▸ finiteLaw_pos_of_mem f ω₀)
  · rw [← hl g]
    exact convolutionPower_pos_list f (l g)
  · exact (Finset.single_le_sum (fun i _ => Nat.zero_le ((l i).length))
      (Finset.mem_univ g)).trans (Nat.le_add_left _ _)

end ReachableRandomWalk

theorem fixed_dimension_sweep_convergence (d : ℕ) :
    Filter.Tendsto (fun t => totalVariation (sweepLaw d t)
      (uniformLaw (Equiv.Perm (Slot d)))) Filter.atTop (nhds 0) := by
  obtain ⟨L, hL, hpos⟩ := finiteLaw_fullSupport_power (binarySweep d)
    (fun _ _ => false) (binarySweep_zero d) (every_permutation_sweepReachable d)
  exact convolutionPower_tendsto_uniform
    ⟨finiteLaw_nonneg (binarySweep d), finiteLaw_sum (binarySweep d)⟩ hL hpos

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_BinaryLineDisk
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma complexLineLaw_real (d : ℕ) (z : ℝ) (g : Equiv.Perm (Slot d)) :
    complexLineLaw d (z:ℂ) g=(lineLaw d z g:ℂ) := by
  simp [complexLineLaw,lineLaw]

lemma complexLine_average {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Slot d)) V)
    (z : ℂ) : complexAverage ρ (complexLineLaw d z)=
      complexAverage ρ (fun g => (uniformLaw (Equiv.Perm (Slot d)) g:ℂ))+
        z • (complexAverage ρ (fun g => (binaryLaw d g:ℂ))-
          complexAverage ρ (fun g => (uniformLaw (Equiv.Perm (Slot d)) g:ℂ))) := by
  ext v
  simp only [complexAverage_apply,complexLineLaw,add_smul,mul_smul,
    Finset.sum_add_distrib,←Finset.smul_sum,add_apply,
    smul_apply,sub_apply]
  module

theorem binary_line_disk (d : ℕ) : ∃ R : ℝ, 1<R ∧
    ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
    ∀ (ρ : Representation ℂ (Equiv.Perm (Slot d)) V),
      (∀g v, ‖ρ g v‖=‖v‖) → ∀z : ℂ, ‖z‖≤R →
        ‖complexAverage ρ (complexLineLaw d z)‖ ≤ 1 := by
  have he : ∀ᶠ n in Filter.atTop,
      totalVariation (sweepLaw d n) (uniformLaw (Equiv.Perm (Slot d)))<1/4 :=
    (fixed_dimension_sweep_convergence d).eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  have ht := (hN (max N 1) (le_max_left _ _)).le
  have hp : IsProbability (binaryLaw d) :=
    ⟨finiteLaw_nonneg _,finiteLaw_sum _⟩
  have hp1 : 0<binaryLaw d 1 := by
    rw [binaryLaw,←binarySweep_zero d]
    exact finiteLaw_pos_of_mem _ _
  obtain ⟨R,hR,h⟩ := finite_average_disk hp hp1 (by omega : 0 < max N 1) ht
  refine ⟨R,hR,?_⟩
  intro V _ _ _ ρ hρ z hz
  rw [complexLine_average]
  exact h V ρ hρ z hz

theorem binary_lines_disk (m : ℕ) : ∃ R : ℝ, 1<R ∧ ∀ d, d ≤ m →
    ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
    ∀ (ρ : Representation ℂ (Equiv.Perm (Slot d)) V),
      (∀g v, ‖ρ g v‖=‖v‖) → ∀z : ℂ, ‖z‖≤R →
        ‖complexAverage ρ (complexLineLaw d z)‖ ≤ 1 := by
  induction m with
  | zero =>
    obtain ⟨R,hR,h⟩ := binary_line_disk 0
    refine ⟨R,hR,?_⟩
    intro d hd
    have : d=0 := by omega
    subst d
    exact h
  | succ m ih =>
    obtain ⟨R,hR,h⟩ := ih
    obtain ⟨S,hS,k⟩ := binary_line_disk (m+1)
    refine ⟨min R S,lt_min hR hS,?_⟩
    intro d hd V _ _ _ ρ hρ z hz
    by_cases he : d=m+1
    · subst d
      exact k V ρ hρ z (hz.trans (min_le_right _ _))
    · exact h d (by omega) V ρ hρ z (hz.trans (min_le_left _ _))

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_ComplexGrid
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

variable {b : ℕ} (bits : Fin b → ℕ)

lemma complexGridWeight_real (z : ℝ) (g : GridChoices bits) :
    complexGridWeight bits (z:ℂ) g=(gridWeight bits z g:ℂ) := by
  simp [complexGridWeight,gridWeight,complexLineLaw_real]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) V)

lemma complexGridAverage_product (z : ℂ) :
    complexGridAverage bits ρ z=(List.ofFn (fun j =>
      complexAverage (ρ.comp (gridStageHom bits j))
        (fun f => ∏y,complexLineLaw (bits j) z (f y)))).reverse.prod := by
  unfold complexGridAverage complexGridWeight gridSweep
  simp_rw [map_list_prod,List.map_reverse,List.map_ofFn,Function.comp_def]
  change (∑g : GridChoices bits, (∏j, ∏y, complexLineLaw (bits j) z (g j y)) •
    (List.ofFn (fun j => continuousRep ρ (gridStageHom bits j (g j)))).reverse.prod)=_
  rw [independent_average_product (X := fun j => GridOutside bits j → Equiv.Perm (Slot (bits j)))
    (fun j f => ∏y,complexLineLaw (bits j) z (f y))
    (fun j f => continuousRep ρ (gridStageHom bits j f))]
  congr 3
  funext j
  rw [complexAverage_sum]
  rfl

lemma complexGridAverage_differentiable : Differentiable ℂ (complexGridAverage bits ρ) := by
  unfold complexGridAverage
  apply Differentiable.fun_sum
  intro g _
  apply Differentiable.fun_smul
  · unfold complexGridWeight
    apply Differentiable.fun_finsetProd
    intro j _
    apply Differentiable.fun_finsetProd
    intro y _
    unfold complexLineLaw
    fun_prop
  · fun_prop

lemma complexGridAverage_norm_le_one [Nontrivial V] (z : ℂ)
    (hρ : ∀g v, ‖ρ g v‖=‖v‖)
    (hline : ∀j : Fin b,
      ∀σ : Representation ℂ (Equiv.Perm (Slot (bits j))) V,
      (∀g v, ‖σ g v‖=‖v‖) → ‖complexAverage σ (complexLineLaw (bits j) z)‖ ≤ 1) :
    ‖complexGridAverage bits ρ z‖ ≤ 1 := by
  rw [complexGridAverage_product]
  apply reverse_product_norm_le_one
  intro j
  exact pi_comp_average_norm_le_one (I := GridOutside bits j)
    (G := Equiv.Perm (Slot (bits j))) (H := Equiv.Perm (GridSlot bits)) (V := V)
    ρ (gridStageHom bits j)
    (complexLineLaw (bits j) z) hρ (hline j)

theorem complex_grid_disk (m : ℕ) : ∃ R : ℝ, 1 < R ∧
    ∀ (b : ℕ) (bits : Fin b → ℕ), (∀ j, bits j ≤ m) →
    ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [FiniteDimensional ℂ V] [Nontrivial V],
    ∀ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) V,
      (∀g v, ‖ρ g v‖=‖v‖) → ∀z : ℂ, ‖z‖ ≤ R →
        ‖complexGridAverage bits ρ z‖ ≤ 1 := by
  obtain ⟨R,hR,h⟩ := binary_lines_disk m
  refine ⟨R,hR,?_⟩
  intro b bits hm V _ _ _ _ ρ hρ z hz
  apply complexGridAverage_norm_le_one bits ρ z hρ
  intro j σ hσ
  exact h (bits j) (hm j) V σ hσ z hz

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IrrepTransport
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators MonoidAlgebra Classical

namespace BinaryCoordinateSweeps.Irrep
variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

lemma irreducible_comp_equiv (e : H ≃* G) (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Representation.IsIrreducible (k := ℂ) (G := H) (V := V) (ρ.comp e.toMonoidHom) :=
  (subrepresentationCongr e ρ).isSimpleOrder_iff.mp inferInstance

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GroupedLogBounds
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical MonoidAlgebra ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation TraceHolder

variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [LinearOrder I]
  {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

lemma irreducible_finrank_pos {G W : Type*} [Group G]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) [ρ.IsIrreducible] : 0<Module.finrank ℂ W := by
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  rw [← ρ.asModuleEquiv.finrank_eq]
  exact Module.finrank_pos

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_OneCard
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma coordinateLayer_apply_at (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i≠j} → Bool) → Bool) (x : Slot d) :
    coordinateLayer d j c x j = (x j ^^ c (fun i => x i)) := by
  simp [coordinateLayer,Equiv.piSplitAt_symm_apply]

lemma coordinateLayer_apply_other (d : ℕ) (j i : Fin d) (hi : i≠j)
    (c : ({i : Fin d // i≠j} → Bool) → Bool) (x : Slot d) :
    coordinateLayer d j c x i = x i := by
  simp [coordinateLayer,Equiv.piSplitAt_symm_apply,hi]

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplitWeights
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit

section
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ)

lemma gridWeight_split (z : ℝ) (g : GridChoices bits) :
    gridWeight bits z g =
      (∏y : GridSlot (rightBits bits), gridWeight (leftBits bits) z (rowChoices bits g y)) *
      (∏x : GridSlot (leftBits bits), gridWeight (rightBits bits) z (columnChoices bits g x)) := by
  unfold gridWeight
  rw [Fin.prod_univ_add]
  congr 1
  · rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    have he := (leftOutsideEquiv bits j).symm.prod_comp (fun u => lineLaw (bits (j.castAdd n)) z (g (j.castAdd n) u))
    rw [Fintype.prod_prod_type] at he
    exact he.symm
  · rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    have he := (rightOutsideEquiv bits j).symm.prod_comp (fun u => lineLaw (bits (j.natAdd m)) z (g (j.natAdd m) u))
    rw [Fintype.prod_prod_type] at he
    exact he.symm

end

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplitSweep
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit

variable {X Y : Type*}

variable {m n : ℕ} (bits : Fin (m+n) → ℕ)

lemma gridLayer_left (g : GridChoices bits) (j : Fin m) (x : GridSlot bits) :
    (slotEquiv bits) (gridLayer bits g (j.castAdd n) x) =
      (gridLayer (leftBits bits) (rowChoices bits g (rightSlot bits x)) j (leftSlot bits x),
        rightSlot bits x) := by
  apply Prod.ext
  · simp only
    funext i
    change gridLayer bits g (j.castAdd n) x (i.castAdd n)=_
    by_cases hi : i=j
    · subst i
      rw [gridLayer_at,gridLayer_at,rowChoices_at]
      rfl
    · rw [gridLayer_other bits g _ _ (fun he => hi (Fin.castAdd_injective m n he)),
        gridLayer_other _ _ _ _ hi]
      rfl
  · funext i
    exact gridLayer_other bits g _ _ (by
      intro he
      have hh := congrArg (fun i : Fin (m+n) => i.val) he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega) x

lemma gridLayer_right (g : GridChoices bits) (j : Fin n) (x : GridSlot bits) :
    (slotEquiv bits) (gridLayer bits g (j.natAdd m) x) =
      (leftSlot bits x,
        gridLayer (rightBits bits) (columnChoices bits g (leftSlot bits x)) j (rightSlot bits x)) := by
  apply Prod.ext
  · funext i
    exact gridLayer_other bits g _ _ (by
      intro he
      have hh := congrArg (fun i : Fin (m+n) => i.val) he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega) x
  · simp only
    funext i
    change gridLayer bits g (j.natAdd m) x (i.natAdd m)=_
    by_cases hi : i=j
    · subst i
      rw [gridLayer_at,gridLayer_at,columnChoices_at]
      rfl
    · rw [gridLayer_other bits g _ _ (fun he => hi (Fin.natAdd_injective n m he)),
        gridLayer_other _ _ _ _ hi]
      rfl

lemma layer_left_congr (g : GridChoices bits) (j : Fin m) :
    (slotEquiv bits).permCongr (gridLayer bits g (j.castAdd n)) =
      rowPerm (fun y => gridLayer (leftBits bits) (rowChoices bits g y) j) := by
  apply Equiv.ext
  intro xy
  have he := gridLayer_left bits g j ((slotEquiv bits).symm xy)
  change (slotEquiv bits) (gridLayer bits g (j.castAdd n) ((slotEquiv bits).symm xy))= _
  rw [he]
  have ht := (slotEquiv bits).apply_symm_apply xy
  rw [show leftSlot bits ((slotEquiv bits).symm xy)=xy.1 from congrArg Prod.fst ht,
    show rightSlot bits ((slotEquiv bits).symm xy)=xy.2 from congrArg Prod.snd ht]
  rfl

lemma layer_right_congr (g : GridChoices bits) (j : Fin n) :
    (slotEquiv bits).permCongr (gridLayer bits g (j.natAdd m)) =
      columnPerm (fun x => gridLayer (rightBits bits) (columnChoices bits g x) j) := by
  apply Equiv.ext
  intro xy
  have he := gridLayer_right bits g j ((slotEquiv bits).symm xy)
  change (slotEquiv bits) (gridLayer bits g (j.natAdd m) ((slotEquiv bits).symm xy))= _
  rw [he]
  have ht := (slotEquiv bits).apply_symm_apply xy
  rw [show leftSlot bits ((slotEquiv bits).symm xy)=xy.1 from congrArg Prod.fst ht,
    show rightSlot bits ((slotEquiv bits).symm xy)=xy.2 from congrArg Prod.snd ht]
  rfl

lemma prod_rows (L : List (Y → Equiv.Perm X)) :
    (L.map rowPerm).prod=rowPerm (fun y => (L.map (fun f => f y)).prod) := by
  induction L with
  | nil => rfl
  | cons f L ih =>
    simp only [List.map_cons,List.prod_cons,ih]
    apply Equiv.ext
    intro xy
    rfl
lemma prod_columns (L : List (X → Equiv.Perm Y)) :
    (L.map columnPerm).prod=columnPerm (fun x => (L.map (fun f => f x)).prod) := by
  induction L with
  | nil => rfl
  | cons f L ih =>
    simp only [List.map_cons,List.prod_cons,ih]
    apply Equiv.ext
    intro xy
    rfl

theorem gridSweep_split (g : GridChoices bits) :
    (slotEquiv bits).permCongr (gridSweep bits g) =
      columnPerm (fun x => gridSweep (rightBits bits) (columnChoices bits g x)) *
        rowPerm (fun y => gridSweep (leftBits bits) (rowChoices bits g y)) := by
  change (slotEquiv bits).permCongrHom (gridSweep bits g)=_
  unfold gridSweep
  rw [List.ofFn_add,List.reverse_append,List.prod_append]
  rw [map_mul]
  congr 1
  · rw [map_list_prod (slotEquiv bits).permCongrHom,List.map_reverse,List.map_ofFn]
    change (List.ofFn (fun j : Fin n => (slotEquiv bits).permCongr (gridLayer bits g (j.natAdd m)))).reverse.prod=_
    simp_rw [layer_right_congr]
    simpa only [List.map_reverse,List.map_ofFn,Function.comp_def] using
      (prod_columns (List.ofFn (fun j : Fin n => fun x =>
        gridLayer (rightBits bits) (columnChoices bits g x) j)).reverse)
  · rw [map_list_prod (slotEquiv bits).permCongrHom,List.map_reverse,List.map_ofFn]
    change (List.ofFn (fun j : Fin m => (slotEquiv bits).permCongr (gridLayer bits g (j.castAdd n)))).reverse.prod=_
    simp_rw [layer_left_congr]
    simpa only [List.map_reverse,List.map_ofFn,Function.comp_def] using
      (prod_rows (List.ofFn (fun j : Fin m => fun y =>
        gridLayer (leftBits bits) (rowChoices bits g y) j)).reverse)

end BinaryCoordinateSweeps.GridSplit

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_OneAxis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma oneAxis_gridWeight (bits : Fin 1 → ℕ) (z : ℝ) (g : GridChoices bits) :
    gridWeight bits z g = lineLaw (bits 0) z (oneAxisChoiceEquiv bits g) := by
  simp [gridWeight, oneAxisChoiceEquiv, Equiv.piUnique, Equiv.funUnique]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_AnalyticTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped Topology
open Set Complex Complex.HadamardThreeLines

namespace BinaryCoordinateSweeps

lemma cosh_norm_le (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  rw [Complex.cosh, norm_div]
  norm_num only [Complex.norm_ofNat]
  rw [Real.cosh_eq]
  have h := norm_add_le (Complex.exp z) (Complex.exp (-z))
  rw [Complex.norm_exp,Complex.norm_exp,Complex.neg_re] at h
  linarith

lemma ellipseMap_norm {v L : ℝ} (hv : 0 ≤ v) (hL : 0 ≤ L) (z : ℂ)
    (hz : z ∈ verticalClosedStrip 0 L) :
    ‖ellipseMap v z‖ ≤ v/2*(Real.cosh L+1) := by
  change 0 ≤ z.re ∧ z.re ≤ L at hz
  have hc : Real.cosh z.re ≤ Real.cosh L := by
    rw [Real.cosh_le_cosh,abs_of_nonneg hz.1,abs_of_nonneg hL]
    exact hz.2
  have hn : ‖Complex.cosh z+1‖ ≤ Real.cosh L+1 := by
    have := norm_add_le (Complex.cosh z) (1:ℂ)
    norm_num only [norm_one] at this
    linarith [cosh_norm_le z]
  simpa only [ellipseMap,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hv,Complex.norm_ofNat] using mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ v/2)

lemma ellipseMap_left {v : ℝ} (hv : 0 ≤ v) (z : ℂ) (hz : z.re=0) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ v ∧ ellipseMap v z=(t:ℂ) := by
  have he : z=(z.im:ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
  refine ⟨v/2*(Real.cos z.im+1),?_,?_,?_⟩
  · have := Real.neg_one_le_cos z.im
    exact mul_nonneg (div_nonneg hv (by norm_num)) (by linarith)
  · have := Real.cos_le_one z.im
    nlinarith
  · have hc : Complex.cosh z=(Real.cos z.im:ℂ) := by
      calc Complex.cosh z = Complex.cosh ((z.im:ℂ)*Complex.I) := congrArg _ he
           _ = (Real.cos z.im:ℂ) := by rw [Complex.cosh_mul_I,Complex.ofReal_cos]
    rw [ellipseMap,hc]
    push_cast
    rfl

theorem analytic_segment_transfer (R a : ℝ) (hR : 1 < R) (ha : 0 < a) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
    ∀ E : Type*, ∀ [NormedAddCommGroup E] [NormedSpace ℂ E],
    ∀ f : ℂ → E, Differentiable ℂ f → ∀ ε : ℝ, 0 ≤ ε →
    (∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ 1) →
    (∀ t : ℝ, 0 ≤ t → t ≤ a → ‖f (t:ℂ)‖ ≤ ε) → ‖f 1‖ ≤ ε^θ := by
  let v := min a (1/2)
  have hv : 0 < v := lt_min ha (by norm_num)
  have hva : v ≤ a := min_le_left _ _
  have hv1 : v < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let x := Real.arcosh (2/v-1)
  let L := Real.arcosh (2*R/v-1)
  have hargx : 1 < 2/v-1 := by
    have : (2:ℝ) < 2/v := (lt_div_iff₀ hv).mpr (by linarith)
    linarith
  have hargL : 2/v-1 < 2*R/v-1 := by
    apply sub_lt_sub_right
    apply (div_lt_div_iff_of_pos_right hv).2
    linarith
  have hx : 0 < x := Real.arcosh_pos hargx
  have hxL : x < L := (Real.arcosh_lt_arcosh (by linarith) (by linarith)).mpr hargL
  have hL : 0 < L := hx.trans hxL
  have hcoshx : Real.cosh x=2/v-1 := Real.cosh_arcosh hargx.le
  have hcoshL : Real.cosh L=2*R/v-1 := Real.cosh_arcosh (hargx.trans hargL).le
  have houter : v/2*(Real.cosh L+1)=R := by rw [hcoshL]; field_simp; ring
  have hat : ellipseMap v (x:ℂ)=1 := by
    rw [ellipseMap,←Complex.ofReal_cosh,hcoshx]
    push_cast
    have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    field_simp [hvC]
    ring
  refine ⟨1-x/L,by have := (div_lt_one hL).mpr hxL; linarith,
    by have := div_nonneg hx.le hL.le; linarith,?_⟩
  intro E _ _ f hf ε hε hbound hsmall
  let F : ℂ → E := fun z => f (ellipseMap v z)
  have hmap : Differentiable ℂ (ellipseMap v) :=
    (Complex.differentiable_cosh.add_const 1).const_mul ((v:ℂ)/2)
  have hFd : Differentiable ℂ F := hf.comp hmap
  have hF1 : ∀z ∈ verticalClosedStrip 0 L, ‖F z‖ ≤ 1 := by
    intro z hz
    exact hbound _ ((ellipseMap_norm hv.le hL.le z hz).trans_eq houter)
  have hc : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 L) := by
    use 1
    rintro y ⟨z,hz,rfl⟩
    exact hF1 z hz
  have hleft : ∀z ∈ Complex.re ⁻¹' {(0:ℝ)}, ‖F z‖ ≤ ε := by
    intro z hz
    obtain ⟨t,ht,htv,he⟩ := ellipseMap_left hv.le z hz
    dsimp [F]
    rw [he]
    exact hsmall t ht (htv.trans hva)
  have hright : ∀z ∈ Complex.re ⁻¹' {L}, ‖F z‖ ≤ 1 := by
    intro z hz
    apply hF1
    change 0 ≤ z.re ∧ z.re ≤ L
    change z.re=L at hz
    rw [hz]
    exact ⟨hL.le,le_rfl⟩
  have ht := norm_le_interp_of_mem_verticalClosedStrip' hL
    (show (x:ℂ) ∈ verticalClosedStrip 0 L from ⟨hx.le,hxL.le⟩)
    hFd.diffContOnCl hc hleft hright
  simpa only [F,hat,Complex.ofReal_re,sub_zero,Real.one_rpow,mul_one] using ht

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

theorem grid_analytic_contraction : ∃ r : ℕ, 0<r ∧ ∃ g : ℝ, 0<g ∧
    ∀b : ℕ, 1≤b → ∀bits : Fin b → ℕ,
    (∀j,r≤bits j ∧ bits j≤2*r) → ∀D : ℕ,
    ∀ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) (RepSpace D),
    ρ.IsIrreducible → IsUnitaryRep ρ →
      ‖complexGridAverage bits ρ 1‖ ≤ (D:ℝ)^(-g) := by
  obtain ⟨r,hr,q,hq,a,ha,hreal⟩ := real_grid_bound
  obtain ⟨R,hR,hdisk⟩ := complex_grid_disk (2*r)
  obtain ⟨θ,hθ,hθ1,htrans⟩ := analytic_segment_transfer R a hR ha
  refine ⟨r,hr,(c0/(2*q))*θ,mul_pos (div_pos (by norm_num [c0]) (by positivity)) hθ,?_⟩
  intro b hb bits hbits D ρ hi hρ
  have := hi
  have : Nontrivial (RepSpace D) :=
    Module.nontrivial_of_finrank_pos (Signed.irreducible_finrank_pos ρ)
  have ht := htrans (RepSpace D →L[ℂ] RepSpace D) (complexGridAverage bits ρ)
    (complexGridAverage_differentiable bits ρ) ((D:ℝ)^(-c0/(2*q))) (by positivity)
    (hdisk b bits (fun j => (hbits j).2) (RepSpace D) ρ hρ)
    (hreal b hb bits hbits D ρ hi hρ)
  rw [←Real.rpow_mul (Nat.cast_nonneg D)] at ht
  have he : (-c0/(2*(q:ℝ)))*θ = -(c0/(2*q)*θ) := by ring
  simpa only [he] using ht

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_BitBlocks
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma exists_bit_blocks (r : ℕ) (hr : 0<r) : ∀d : ℕ, r≤d →
    ∃b : ℕ, 1≤b ∧ ∃bits : Fin b → ℕ,
      (∀j,r≤bits j ∧ bits j≤2*r) ∧ ∑j,bits j=d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    by_cases hsmall : d≤2*r
    · refine ⟨1,by omega,fun _ => d,fun _ => ⟨hd,hsmall⟩,?_⟩
      simp
    obtain ⟨b,hb,bits,hbits,hsum⟩ := ih (d-r) (by omega) (by omega)
    refine ⟨b+1,by omega,Fin.cons r bits,?_,?_⟩
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero]; omega
      · simpa using hbits i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,hsum,Nat.add_sub_of_le hd]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_FiniteLawAverage
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma finiteLaw_pushLaw {A B : Type*} [Fintype A] [Fintype B] (f : A → B) :
    finiteLaw f=pushLaw (uniformLaw A) f := rfl

lemma pushLaw_expectation {A B R : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid R] [Module ℝ R] (p : A → ℝ) (f : A → B) (F : B → R) :
    (∑b,pushLaw p f b • F b)=∑a,p a • F (f a) := by
  unfold pushLaw
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  simp [ite_smul]

lemma pushLaw_comp {A B C : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (f : A → B) (g : B → C) :
    pushLaw (pushLaw p f) g=pushLaw p (g ∘ f) := by
  funext c
  have he := pushLaw_expectation p f (fun b => if g b=c then (1:ℝ) else 0)
  simpa [pushLaw,smul_eq_mul,mul_ite] using he

lemma pushLaw_equiv {A B C : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → ℝ) (f : B → C) :
    pushLaw (p ∘ e) (f ∘ e)=pushLaw p f := by
  funext c
  exact e.sum_comp (fun b => if f b=c then p b else 0)

lemma pushLaw_equiv_apply {A B : Type*} [Fintype A]
    (e : A ≃ B) (p : A → ℝ) (b : B) : pushLaw p e b=p (e.symm b) := by
  simp only [pushLaw,←e.eq_symm_apply]
  simp

lemma pushLaw_id {A : Type*} [Fintype A] (p : A → ℝ) : pushLaw p id=p := by
  funext a; simp [pushLaw]

lemma pushLaw_prod {A B X Y : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f : A → X) (g : B → Y) :
    pushLaw (fun ab : A×B => p ab.1*q ab.2) (Prod.map f g)=
      fun xy => pushLaw p f xy.1 * pushLaw q g xy.2 := by
  funext xy
  simp only [pushLaw,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun b a => (if f a=xy.1 then p a else 0)*(if g b=xy.2 then q b else 0))]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rcases xy with ⟨x,y⟩
  simp only [Prod.map_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

lemma pushLaw_pi {I : Type*} [Fintype I] [DecidableEq I] {A X : I → Type*}
    [∀i,Fintype (A i)] [∀i,Fintype (X i)]
    (p : ∀i,A i → ℝ) (f : ∀i,A i → X i) :
    pushLaw (fun a : ∀i,A i => ∏i,p i (a i)) (fun a i => f i (a i))=
      fun x => ∏i,pushLaw (p i) (f i) (x i) := by
  funext x
  unfold pushLaw
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [funext_iff]
  by_cases h : ∀i,f i (a i)=x i
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [ite_eq_right (by aesop)]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma uniformLaw_prod {A B : Type*} [Fintype A] [Fintype B] :
    uniformLaw (A×B)=fun ab => uniformLaw A ab.1 * uniformLaw B ab.2 := by
  funext ab
  simp [uniformLaw,Fintype.card_prod,mul_comm]

lemma uniformLaw_pi {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*} [∀i,Fintype (A i)] :
    uniformLaw (∀i,A i)=fun a => ∏i,uniformLaw (A i) (a i) := by
  funext a
  simp [uniformLaw,Fintype.card_pi,Finset.prod_inv_distrib]

lemma uniformLaw_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    uniformLaw B ∘ e=uniformLaw A := by
  funext a
  simp [uniformLaw,Fintype.card_congr e]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_BoardLaw
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open GridSplit

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

lemma boardSampleLaw {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f : A → Equiv.Perm X) (g : B → Equiv.Perm Y) :
    pushLaw (fun LR : (Y → A)×(X → B) => (∏y,p (LR.1 y))*(∏x,q (LR.2 x)))
      (fun LR => columnPerm (g ∘ LR.2) * rowPerm (f ∘ LR.1))=
      boardLaw (pushLaw p f) (pushLaw q g) := by
  have he := pushLaw_prod (fun L : Y → A => ∏y,p (L y)) (fun R : X → B => ∏x,q (R x))
    (fun L y => f (L y)) (fun R x => g (R x))
  rw [pushLaw_pi,pushLaw_pi] at he
  unfold boardLaw boardWeight
  rw [←he,pushLaw_comp]
  rfl

variable {X' Y' : Type*} [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y']

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y'] in
lemma rowPerm_congr (e : X ≃ X') (f : Y ≃ Y') (L : Y → Equiv.Perm X) :
    (Equiv.prodCongr e f).permCongr (rowPerm L)=
      rowPerm (f.arrowCongr e.permCongr L) := by
  apply Equiv.ext
  intro xy
  apply Prod.ext <;> simp [rowPerm,Equiv.permCongr_apply,Equiv.arrowCongr_apply]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y'] in
lemma columnPerm_congr (e : X ≃ X') (f : Y ≃ Y') (R : X → Equiv.Perm Y) :
    (Equiv.prodCongr e f).permCongr (columnPerm R)=
      columnPerm (e.arrowCongr f.permCongr R) := by
  apply Equiv.ext
  intro xy
  apply Prod.ext <;> simp [columnPerm,Equiv.permCongr_apply,Equiv.arrowCongr_apply]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y'] in
lemma boardSweep_congr (e : X ≃ X') (f : Y ≃ Y') (LR : BoardChoices X Y) :
    (Equiv.prodCongr e f).permCongr (boardSweep LR)=
      boardSweep (boardChoicesEquiv e f LR) := by
  change (Equiv.prodCongr e f).permCongrHom (columnPerm LR.2 * rowPerm LR.1)=_
  rw [map_mul]
  change (Equiv.prodCongr e f).permCongr (columnPerm LR.2) *
    (Equiv.prodCongr e f).permCongr (rowPerm LR.1)=_
  rw [rowPerm_congr,columnPerm_congr]
  rfl

omit [DecidableEq X'] [DecidableEq Y'] in
lemma boardWeight_congr (e : X ≃ X') (f : Y ≃ Y')
    (p : Equiv.Perm X → ℝ) (q : Equiv.Perm Y → ℝ) (LR : BoardChoices X Y) :
    boardWeight (pushLaw p e.permCongr) (pushLaw q f.permCongr)
      (boardChoicesEquiv e f LR)=boardWeight p q LR := by
  unfold boardWeight boardChoicesEquiv
  simp only [Equiv.prodCongr_apply,pushLaw_equiv_apply]
  rw [←f.prod_comp,←e.prod_comp]
  have he (σ : Equiv.Perm X) : e.symm.permCongr (e.permCongr σ)=σ :=
    e.permCongr.symm_apply_apply σ
  have hf (σ : Equiv.Perm Y) : f.symm.permCongr (f.permCongr σ)=σ :=
    f.permCongr.symm_apply_apply σ
  simp [Equiv.arrowCongr_apply,he,hf]

lemma boardLaw_congr (e : X ≃ X') (f : Y ≃ Y')
    (p : Equiv.Perm X → ℝ) (q : Equiv.Perm Y → ℝ) :
    pushLaw (boardLaw p q) (Equiv.prodCongr e f).permCongr=
      boardLaw (pushLaw p e.permCongr) (pushLaw q f.permCongr) := by
  unfold boardLaw
  rw [pushLaw_comp]
  have hw : boardWeight (pushLaw p e.permCongr) (pushLaw q f.permCongr) ∘
      boardChoicesEquiv e f=boardWeight p q := funext (boardWeight_congr e f p q)
  have hs : (Equiv.prodCongr e f).permCongr ∘ boardSweep=
      boardSweep ∘ boardChoicesEquiv e f := funext (boardSweep_congr e f)
  rw [hs,←hw]
  exact pushLaw_equiv (boardChoicesEquiv e f) _ _

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {X Y A B Ω : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Fintype A] [Fintype B] [Fintype Ω]
lemma board_equiv_sample (p : A → ℝ) (q : B → ℝ)
    (f : A → Equiv.Perm X) (g : B → Equiv.Perm Y)
    (e : Ω ≃ (Y → A)×(X → B)) (w : Ω → ℝ) (F : Ω → Equiv.Perm (X×Y))
    (hw : ∀c,w c=(∏y,p ((e c).1 y))*(∏x,q ((e c).2 x)))
    (hF : ∀c,F c=GridSplit.columnPerm (g ∘ (e c).2)*GridSplit.rowPerm (f ∘ (e c).1)) :
    pushLaw w F=boardLaw (pushLaw p f) (pushLaw q g) := by
  have hw' : w=(fun LR : (Y→A)×(X→B) => (∏y,p (LR.1 y))*(∏x,q (LR.2 x))) ∘ e := funext hw
  have hf' : F=(fun LR : (Y→A)×(X→B) => GridSplit.columnPerm (g ∘ LR.2)*GridSplit.rowPerm (f ∘ LR.1)) ∘ e := funext hF
  rw [hw',hf',pushLaw_equiv]
  exact boardSampleLaw p q f g
end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_BinarySplitChoices
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.BinarySplit
open GridSplit

variable {m n : ℕ}

lemma rowChoices_at (c : SweepCoins (m+n)) (x : Slot (m+n)) (j : Fin m) :
    rowChoices c (Signed.splitWord x).2 j (fun i => (Signed.splitWord x).1 i)=
      c (j.castAdd n) (fun i => x i) := by
  unfold rowChoices
  congr 1
  apply (leftOutsideEquiv j).injective
  rw [Equiv.apply_symm_apply]
  rfl

lemma columnChoices_at (c : SweepCoins (m+n)) (x : Slot (m+n)) (j : Fin n) :
    columnChoices c (Signed.splitWord x).1 j (fun i => (Signed.splitWord x).2 i)=
      c (j.natAdd m) (fun i => x i) := by
  unfold columnChoices
  congr 1
  apply (rightOutsideEquiv j).injective
  rw [Equiv.apply_symm_apply]
  rfl

lemma layer_left (c : SweepCoins (m+n)) (j : Fin m) (x : Slot (m+n)) :
    Signed.splitWord (coordinateLayer (m+n) (j.castAdd n) (c (j.castAdd n)) x)=
      (coordinateLayer m j (rowChoices c (Signed.splitWord x).2 j) (Signed.splitWord x).1,
        (Signed.splitWord x).2) := by
  apply Prod.ext
  · dsimp only
    funext i
    change coordinateLayer _ _ _ x (i.castAdd n)=_
    by_cases hi : i=j
    · subst i
      rw [coordinateLayer_apply_at,coordinateLayer_apply_at,rowChoices_at]
      rfl
    · rw [coordinateLayer_apply_other _ _ _ (fun he => hi (Fin.ext
        (congrArg (fun i : Fin (m+n) => i.val) he))),coordinateLayer_apply_other _ _ _ hi]
      rfl
  · dsimp only
    funext i
    exact coordinateLayer_apply_other (m+n) (j.castAdd n) (i.natAdd m) (by
      intro he
      have hh := congrArg (fun i : Fin (m+n) => i.val) he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega) _ x

lemma layer_right (c : SweepCoins (m+n)) (j : Fin n) (x : Slot (m+n)) :
    Signed.splitWord (coordinateLayer (m+n) (j.natAdd m) (c (j.natAdd m)) x)=
      ((Signed.splitWord x).1,
        coordinateLayer n j (columnChoices c (Signed.splitWord x).1 j) (Signed.splitWord x).2) := by
  apply Prod.ext
  · dsimp only
    funext i
    exact coordinateLayer_apply_other (m+n) (j.natAdd m) (i.castAdd n) (by
      intro he
      have hh := congrArg (fun i : Fin (m+n) => i.val) he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega) _ x
  · dsimp only
    funext i
    change coordinateLayer _ _ _ x (i.natAdd m)=_
    by_cases hi : i=j
    · subst i
      rw [coordinateLayer_apply_at,coordinateLayer_apply_at,columnChoices_at]
      rfl
    · rw [coordinateLayer_apply_other _ _ _ (fun he => hi (Fin.ext (by
        have hh := congrArg (fun i : Fin (m+n) => i.val) he; simpa using hh))),
        coordinateLayer_apply_other _ _ _ hi]
      rfl

lemma layer_left_congr (c : SweepCoins (m+n)) (j : Fin m) :
    Signed.splitWord.permCongr (coordinateLayer (m+n) (j.castAdd n) (c (j.castAdd n)))=
      rowPerm (fun y => coordinateLayer m j (rowChoices c y j)) := by
  apply Equiv.ext
  intro xy
  have he := layer_left c j (Signed.splitWord.symm xy)
  change Signed.splitWord (coordinateLayer _ _ _ (Signed.splitWord.symm xy))=_
  rw [he,Equiv.apply_symm_apply]
  rfl

lemma layer_right_congr (c : SweepCoins (m+n)) (j : Fin n) :
    Signed.splitWord.permCongr (coordinateLayer (m+n) (j.natAdd m) (c (j.natAdd m)))=
      columnPerm (fun x => coordinateLayer n j (columnChoices c x j)) := by
  apply Equiv.ext
  intro xy
  have he := layer_right c j (Signed.splitWord.symm xy)
  change Signed.splitWord (coordinateLayer _ _ _ (Signed.splitWord.symm xy))=_
  rw [he,Equiv.apply_symm_apply]
  rfl

theorem binarySweep_split (c : SweepCoins (m+n)) :
    Signed.splitWord.permCongr (binarySweep (m+n) c)=
      columnPerm (fun x => binarySweep n (columnChoices c x)) *
        rowPerm (fun y => binarySweep m (rowChoices c y)) := by
  change Signed.splitWord.permCongrHom (binarySweep (m+n) c)=_
  unfold binarySweep
  rw [List.ofFn_add,List.reverse_append,List.prod_append,map_mul]
  congr 1
  · rw [map_list_prod Signed.splitWord.permCongrHom,List.map_reverse,List.map_ofFn]
    change (List.ofFn (fun j : Fin n => Signed.splitWord.permCongr
      (coordinateLayer _ (j.natAdd m) (c (j.natAdd m))))).reverse.prod=_
    simp_rw [layer_right_congr]
    simpa only [List.map_reverse,List.map_ofFn,Function.comp_def] using
      (prod_columns (List.ofFn (fun j : Fin n => fun x =>
        coordinateLayer n j (columnChoices c x j))).reverse)
  · rw [map_list_prod Signed.splitWord.permCongrHom,List.map_reverse,List.map_ofFn]
    change (List.ofFn (fun j : Fin m => Signed.splitWord.permCongr
      (coordinateLayer _ (j.castAdd n) (c (j.castAdd n))))).reverse.prod=_
    simp_rw [layer_left_congr]
    simpa only [List.map_reverse,List.map_ofFn,Function.comp_def] using
      (prod_rows (List.ofFn (fun j : Fin m => fun y =>
        coordinateLayer m j (rowChoices c y j))).reverse)

end BinaryCoordinateSweeps.BinarySplit

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
open GridSplit

lemma pushLaw_inverse {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : A → ℝ) : pushLaw (pushLaw p e) e.symm=p := by
  rw [pushLaw_comp]
  have he : e.symm ∘ e = id := funext e.symm_apply_apply
  rw [he,pushLaw_id]

lemma pushLaw_injective {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) : Function.Injective (fun p : A → ℝ => pushLaw p e) := by
  intro p q he
  have hh := congrArg (fun w => pushLaw w e.symm) he
  simpa only [pushLaw_inverse] using hh

lemma binary_splitLaw (m n : ℕ) :
    pushLaw (binaryLaw (m+n)) Signed.splitWord.permCongr=
      boardLaw (binaryLaw m) (binaryLaw n) := by
  unfold binaryLaw
  rw [finiteLaw_pushLaw,finiteLaw_pushLaw,finiteLaw_pushLaw,pushLaw_comp]
  let e := BinarySplit.choicesEquiv (m:=m) (n:=n)
  have hs : Signed.splitWord.permCongr ∘ binarySweep (m+n)=
      (fun LR : (Slot n → SweepCoins m) × (Slot m → SweepCoins n) =>
        columnPerm (binarySweep n ∘ LR.2)*rowPerm (binarySweep m ∘ LR.1)) ∘ e :=
    funext BinarySplit.binarySweep_split
  rw [hs,←uniformLaw_equiv e,pushLaw_equiv]
  have hu : uniformLaw ((Slot n → SweepCoins m)×(Slot m → SweepCoins n))=
      fun LR => (∏y,uniformLaw (SweepCoins m) (LR.1 y))*
        (∏x,uniformLaw (SweepCoins n) (LR.2 x)) := by
    rw [uniformLaw_prod]
    simp only [uniformLaw_pi (I:=Slot n) (A:=fun _ => SweepCoins m),
      uniformLaw_pi (I:=Slot m) (A:=fun _ => SweepCoins n)]
  rw [hu]
  exact boardSampleLaw _ _ _ _

lemma grid_splitLaw {m n : ℕ} (bits : Fin (m+n) → ℕ) :
    pushLaw (gridLaw bits) (slotEquiv (m:=m) (n:=n) bits).permCongr=
      boardLaw (gridLaw (leftBits (m:=m) (n:=n) bits)) (gridLaw (rightBits (m:=m) (n:=n) bits)) := by
  let : DecidableEq (GridSlot (leftBits (m:=m) (n:=n) bits)) := inferInstance
  let : DecidableEq (GridSlot (rightBits (m:=m) (n:=n) bits)) := inferInstance
  let : Fintype (GridChoices (leftBits (m:=m) (n:=n) bits)) := inferInstance
  let : Fintype (GridChoices (rightBits (m:=m) (n:=n) bits)) := inferInstance
  unfold gridLaw
  rw [pushLaw_comp]
  exact board_equiv_sample
    (gridWeight (leftBits (m:=m) (n:=n) bits) 1)
    (gridWeight (rightBits (m:=m) (n:=n) bits) 1)
    (gridSweep (leftBits (m:=m) (n:=n) bits))
    (gridSweep (rightBits (m:=m) (n:=n) bits))
    (GridSplit.choicesEquiv (m:=m) (n:=n) bits) _ _
    (gridWeight_split (m:=m) (n:=n) bits 1) (gridSweep_split (m:=m) (n:=n) bits)

lemma oneAxis_gridLaw (bits : Fin 1 → ℕ) :
    pushLaw (gridLaw bits) (oneAxisSlotEquiv bits).permCongr=binaryLaw (bits 0) := by
  unfold gridLaw
  rw [pushLaw_comp]
  have hw : gridWeight bits 1=binaryLaw (bits 0) ∘ oneAxisChoiceEquiv bits := by
    funext c
    simp [oneAxis_gridWeight,lineLaw]
  have hs : (oneAxisSlotEquiv bits).permCongr ∘ gridSweep bits=oneAxisChoiceEquiv bits := by
    funext c
    rw [Function.comp_apply,←oneAxisSweepEquiv_apply]
    exact (oneAxisSlotEquiv bits).permCongr.apply_symm_apply _
  rw [hw,hs]
  have hh := pushLaw_equiv (oneAxisChoiceEquiv bits) (binaryLaw (bits 0)) id
  simpa only [Function.id_comp,pushLaw_id] using hh

theorem gridLaw_binary : ∀b : ℕ, 1≤b → ∀bits : Fin b → ℕ,
    ∃d : ℕ, d=∑j,bits j ∧ ∃e : GridSlot bits ≃ Slot d,
      pushLaw (gridLaw bits) e.permCongr=binaryLaw d := by
  intro b
  induction b using Nat.case_strong_induction_on with
  | hz => intro hb; omega
  | hi b ih =>
    intro hb bits
    by_cases hb0 : b=0
    · subst b
      exact ⟨bits 0,by simp,oneAxisSlotEquiv bits,oneAxis_gridLaw bits⟩
    obtain ⟨dL,hdL,eL,heL⟩ := ih b (by omega) (by omega) (leftBits (n:=1) bits)
    let eR := oneAxisSlotEquiv (rightBits (m:=b) bits)
    have heR := oneAxis_gridLaw (rightBits (m:=b) bits)
    let dR := rightBits (m:=b) (n:=1) bits 0
    let ep := Equiv.prodCongr eL eR
    let e := ((slotEquiv (m:=b) (n:=1) bits).trans ep).trans Signed.splitWord.symm
    refine ⟨dL+dR,?_,e,?_⟩
    · rw [Fin.sum_univ_add,←hdL]
      simp [dR]
    · apply pushLaw_injective Signed.splitWord.permCongr
      change pushLaw (pushLaw (gridLaw bits) e.permCongr) Signed.splitWord.permCongr=
        pushLaw (binaryLaw (dL+dR)) Signed.splitWord.permCongr
      rw [binary_splitLaw,pushLaw_comp]
      have he : Signed.splitWord.permCongr ∘ e.permCongr=
          ep.permCongr ∘ (slotEquiv (m:=b) (n:=1) bits).permCongr := by
        funext σ
        apply Equiv.ext
        intro xy
        simp [e,Equiv.permCongr_apply]
      let : DecidableEq (GridSlot (leftBits (m:=b) (n:=1) bits) × GridSlot (rightBits (m:=b) (n:=1) bits)) := inferInstance
      rw [he,←pushLaw_comp (gridLaw bits) (slotEquiv (m:=b) (n:=1) bits).permCongr ep.permCongr]
      rw [grid_splitLaw (m:=b) (n:=1)]
      change pushLaw (boardLaw _ _) (Equiv.prodCongr eL eR).permCongr = _
      rw [boardLaw_congr eL eR,heL,heR]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_BinaryContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma averageOperator_sum {G : Type*} [Fintype G] [Monoid G] {D : ℕ}
    (p : G → ℝ) (ρ : Representation ℂ G (RepSpace D)) :
    averageOperator p ρ=∑g,(p g:ℂ) • Module.End.toContinuousLinearMap (RepSpace D) (ρ g) := by
  apply ContinuousLinearMap.coe_injective
  simp [averageOperator,Module.End.toContinuousLinearMap]

lemma pushLaw_complex_expectation {A B R : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid R] [Module ℂ R] (p : A → ℝ) (f : A → B) (F : B → R) :
    (∑b,(pushLaw p f b:ℂ) • F b)=∑a,(p a:ℂ) • F (f a) := by
  unfold pushLaw
  simp only [Complex.ofReal_sum,apply_ite,Complex.ofReal_zero,Finset.sum_smul]
  rw [Finset.sum_comm]
  simp [ite_smul]

lemma gridAverage_relabel {b D d : ℕ} (bits : Fin b → ℕ) (e : GridSlot bits ≃ Slot d)
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D))
    (he : pushLaw (gridLaw bits) e.permCongr=binaryLaw d) :
    complexGridAverage bits (ρ.comp e.permCongrHom.toMonoidHom) 1=
      averageOperator (binaryLaw d) ρ := by
  rw [averageOperator_sum,←he,pushLaw_complex_expectation]
  unfold gridLaw
  rw [pushLaw_complex_expectation]
  unfold complexGridAverage
  apply Finset.sum_congr rfl
  intro c _
  rw [show (1:ℂ)=(1:ℝ) from rfl,complexGridWeight_real]
  rfl

theorem binary_contraction : BinaryContractionTarget := by
  obtain ⟨r,hr,g,hg,hgrid⟩ := grid_analytic_contraction
  refine ⟨g,hg,r,?_⟩
  intro d hd D ρ hi hu
  have := hi
  obtain ⟨b,hb,bits,hbits,hsum⟩ := exists_bit_blocks r hr d hd
  obtain ⟨d',hd',e,he⟩ := gridLaw_binary b hb bits
  have hdd : d'=d := hd'.trans hsum
  cases hdd
  have hσ : Representation.IsIrreducible (ρ.comp e.permCongrHom.toMonoidHom) :=
    Irrep.irreducible_comp_equiv e.permCongrHom ρ
  have hunit : IsUnitaryRep (ρ.comp e.permCongrHom.toMonoidHom) := fun g v => hu _ _
  have hh := hgrid b hb bits hbits D (ρ.comp e.permCongrHom.toMonoidHom) hσ hunit
  rwa [gridAverage_relabel bits e ρ he] at hh

open Irrep

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_BinaryMixingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young

theorem uniform_sweep_mixing : UniformSweepMixingTarget := by
  obtain ⟨w,hw⟩ := constant_sweep_mixing
  refine ⟨w,?_⟩
  intro ε hε
  obtain ⟨d₀,hd₀⟩ := hw ε hε
  exact ⟨d₀,fun d hd τ => (hd₀ d hd τ).le⟩

theorem binary_main : BinaryMainTarget :=
  ⟨binary_contraction,binary_sign_annihilated,uniform_sweep_mixing⟩

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

theorem binary_sweep_contraction_and_mixing_oai :
    BinaryCoordinateSweeps.BinaryContractionTarget ∧
    (∀ d : ℕ, 0 < d → ∑ g : Equiv.Perm (BinaryCoordinateSweeps.Slot d),
      BinaryCoordinateSweeps.binaryLaw d g * BinaryCoordinateSweeps.realSign g = 0) ∧
    BinaryCoordinateSweeps.UniformSweepMixingTarget :=
  BinaryCoordinateSweeps.binary_main

end OAI
end

theorem solution : type_of% @OAI.binary_sweep_contraction_and_mixing_oai := @OAI.binary_sweep_contraction_and_mixing_oai
