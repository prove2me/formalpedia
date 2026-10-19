-- Prove2me | solution 1 for QAlgorithms.DeWolf.simon_algorithm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T21:48:31.24121+00:00
-- url     : https://prove2.me/submissions/54849c6a-afb6-41be-b9b9-97481e698d5a

import Definitions.Def_QAlgorithms_DeWolf_Ch03_Model
import Theorems.Thm_QAlgorithms_gf2_nullvector_circuit
import Theorems.Thm_QAlgorithms_Nannicini_simon_linearIndependent_prob
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open QAlgorithms QAlgorithms.DeWolf Classical Module Submodule
open scoped BigOperators ENNReal

private def bit : Bool →+ ZMod 2 where
  toFun b := if b then 1 else 0
  map_zero' := rfl
  map_add' a b := by cases a <;> cases b <;> decide

private def bitsEquiv (n : ℕ) : Qubits n ≃ (Fin n → ZMod 2) :=
  Equiv.piCongrRight fun _ =>
    { toFun := bit
      invFun := fun z => z = 1
      left_inv := fun b => by cases b <;> decide
      right_inv := fun z => by fin_cases z <;> rfl }

private lemma bits_eq {n : ℕ} (b : Qubits n) : bitsEquiv n b = simonBitsToZMod2 b := rfl

private lemma dot_bits {n : ℕ} (a b : Qubits n) :
    simonBitsToZMod2 a ⬝ᵥ simonBitsToZMod2 b = bit (dotBits a b) := by
  rw [dotBits, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (if a i then (1 : ZMod 2) else 0) * (if b i then 1 else 0) = bit (a i && b i)
  cases a i <;> cases b i <;> rfl

private lemma dot_zero {n : ℕ} (a b : Qubits n) :
    simonBitsToZMod2 a ⬝ᵥ simonBitsToZMod2 b = 0 ↔ dotBits a b = false := by
  rw [dot_bits]
  cases dotBits a b <;> decide

private lemma bits_ne_zero {n : ℕ} {s : Qubits n} (hs : s ≠ 0) : simonBitsToZMod2 s ≠ 0 := by
  intro h
  apply hs
  apply (bitsEquiv n).injective
  change simonBitsToZMod2 s = simonBitsToZMod2 0
  have hz : simonBitsToZMod2 (0 : Qubits n) = 0 := by ext i; rfl
  rw [hz]; exact h

private noncomputable def dotMap {n : ℕ} (a : Fin n → ZMod 2) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := v ⬝ᵥ a
  map_add' x y := add_dotProduct x y a
  map_smul' c x := smul_dotProduct c x a

private lemma dotMap_ne {n : ℕ} {a : Fin n → ZMod 2} (ha : a ≠ 0) : dotMap a ≠ 0 := by
  intro h
  apply ha
  ext i
  have := congrArg (fun f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 => f (Pi.single i 1)) h
  simpa [dotMap, single_dotProduct] using this

private lemma kernel_dim {n : ℕ} {a : Fin n → ZMod 2} (ha : a ≠ 0) :
    finrank (ZMod 2) (LinearMap.ker (dotMap a)) = n - 1 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero (dotMap_ne ha)
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

private lemma zmod_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma unique_mask {n : ℕ} (s : Qubits n) (hs : s ≠ 0)
    (m : ℕ) (js : Fin m → Qubits n) (hjs : ∀ k, dotBits s (js k) = false)
    (hr : n - 1 ≤ simonSpanRank js) (y : Qubits n) (hy : y ≠ 0)
    (hjy : ∀ k, dotBits (js k) y = false) : y = s := by
  let a := simonBitsToZMod2 s
  let b := simonBitsToZMod2 y
  let W := span (ZMod 2) (Set.range fun k => simonBitsToZMod2 (js k))
  have ha : a ≠ 0 := bits_ne_zero hs
  have hb : b ≠ 0 := bits_ne_zero hy
  have hWa : W ≤ LinearMap.ker (dotMap a) := by
    apply span_le.mpr
    rintro _ ⟨k,rfl⟩
    exact (dot_zero _ _).mpr (by simpa [dotBits, Bool.and_comm] using hjs k)
  have hWb : W ≤ LinearMap.ker (dotMap b) := by
    apply span_le.mpr
    rintro _ ⟨k,rfl⟩
    exact (dot_zero _ _).mpr (hjy k)
  have hW : W = LinearMap.ker (dotMap a) :=
    eq_of_le_of_finrank_le hWa ((kernel_dim ha).symm ▸ hr)
  obtain ⟨i, hi⟩ : ∃ i, a i = 1 := by
    obtain ⟨i,hi⟩ := Function.ne_iff.mp ha
    exact ⟨i, (zmod_cases (a i)).resolve_left hi⟩
  have hcoord (j : Fin n) : b j = a j * b i := by
    have hv : Pi.single j 1 - a j • Pi.single i 1 ∈ W := by
      rw [hW]
      change (Pi.single j 1 - a j • Pi.single i 1) ⬝ᵥ a = 0
      simp [sub_dotProduct, smul_dotProduct, single_dotProduct, hi]
    have hz := hWb hv
    change (Pi.single j 1 - a j • Pi.single i 1) ⬝ᵥ b = 0 at hz
    simpa [sub_dotProduct, smul_dotProduct, single_dotProduct, sub_eq_zero] using hz
  have hbi : b i = 1 := by
    by_contra h
    have h0 : b i = 0 := (zmod_cases (b i)).resolve_right h
    apply hb
    ext j
    simp [hcoord j, h0]
  apply (bitsEquiv n).injective
  change b = a
  ext j
  simp [hcoord j, hbi]

private def sig (b : Bool) : ℂ := if b then -1 else 1

private lemma sig_add (a b : Bool) : sig (a + b) = sig a * sig b := by
  cases a <;> cases b <;> norm_num [sig, Bool.add_eq_xor, Bool.zero_eq_false]

private lemma dot_add {n : ℕ} (a b c : Qubits n) :
    dotBits a (b + c) = dotBits a b + dotBits a c := by
  have h (i : Fin n) : (a i && (b i + c i)) = (a i && b i) + (a i && c i) := by
    cases a i <;> cases b i <;> cases c i <;> decide
  simp only [dotBits, Pi.add_apply, h, Finset.sum_add_distrib]

private lemma Hentry {n : ℕ} (a b : Qubits n) :
    hadamardN n a b = (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * sig (dotBits a b) := by
  have hc : dotBits b a = dotBits a b := by simp only [dotBits, Bool.and_comm]
  simp only [hadamardN, Matrix.of_apply, sig, hc]
  split_ifs <;> ring

private lemma normalization (n : ℕ) :
    ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)) ^ 2 = ((2 : ℂ)^n)⁻¹ := by
  have h : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)^2 = (2 : ℂ)⁻¹ := by
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hn : Real.sqrt (2:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have : ((Real.sqrt (2:ℝ))⁻¹)^2 = (2:ℝ)⁻¹ := by field_simp; nlinarith
    simpa only [Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_ofNat] using congrArg Complex.ofReal this
  push_cast at h ⊢
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, h, inv_pow]

private lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) : act (A * B) v = act A (act B v) := by
  exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec _ _ _).symm

private lemma state_apply {n : ℕ} (x : Qubits n → Qubits n) (j y : Qubits n) :
    simonRunState x (j,y) = ((2:ℂ)^n)⁻¹ * ∑ i, if x i = y then sig (dotBits j i) else 0 := by
  rw [simonRunState, act_mul, act_mul]
  have hi : act (Matrix.kronecker (hadamardN n) (1 : Matrix (Qubits n) (Qubits n) ℂ)) (ket (0,0)) =
      tensorVec (WithLp.toLp 2 (fun _ => (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ))) (ket (0 : Qubits n)) := by
    ext p
    have hz : dotBits p.1 0 = false := by simp only [dotBits, Pi.zero_apply, Bool.zero_eq_false, Bool.and_false]; exact Finset.sum_const_zero
    simp [act, ket, Matrix.kronecker, Matrix.one_apply, Hentry, hz, sig, tensorVec]
  rw [hi]
  have hq : act (xorOracle x)
      (tensorVec (WithLp.toLp 2 (fun _ : Qubits n => (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)))
        (ket (0 : Qubits n))) =
      WithLp.toLp 2 (fun p => if p.2 = x p.1 then (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) else 0) := by
    ext p
    simp [act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, xorOracle,
      tensorVec, ket, PiLp.single_apply, PiLp.toLp_apply, ite_and, eq_comm]
  rw [hq]
  simp only [act, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Hentry]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : x i = y
  · simp only [h, if_true]
    rw [show (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * sig (dotBits j i) *
      (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) =
      (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)^2 * sig (dotBits j i) by ring, normalization]
  · simp [h, Ne.symm h]

private lemma fiber_sum {n : ℕ} (x : Qubits n → Qubits n) (s : Qubits n)
    (hx : SimonPromise x s) (hs : s ≠ 0) (t : Qubits n) (c : Qubits n → ℂ) :
    ∑ i, (if x i = x t then c i else 0) = c t + c (t + s) := by
  have hne : t ≠ t + s := by
    intro h
    have := add_left_cancel (show t + 0 = t + s by simpa using h)
    exact hs this.symm
  have hmem (i : Qubits n) : x i = x t ↔ i ∈ ({t, t+s} : Finset (Qubits n)) := by
    simp [hx i t]
  simp_rw [hmem]
  rw [← Finset.sum_filter]
  rw [show Finset.univ.filter (fun i => i ∈ ({t, t+s} : Finset (Qubits n))) = {t,t+s} by ext; simp]
  simp [hne]

private lemma fiber_card_total {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (x : A → B) :
    ∑ y, Fintype.card {i // x i = y} = Fintype.card A := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv x)

private lemma sampling {n : ℕ} (x : Qubits n → Qubits n) (s : Qubits n)
    (hx : SimonPromise x s) (hs : s ≠ 0) (j : Qubits n) :
    marginalFst (simonRunState x) j = if dotBits s j = false then 2 / (2:ℝ)^n else 0 := by
  have hc : dotBits j s = dotBits s j := by simp [dotBits, Bool.and_comm]
  have hp (y : Qubits n) : prob (simonRunState x) (j,y) =
      ((2:ℝ)^n)⁻¹ ^ 2 * ‖∑ i, if x i = y then sig (dotBits j i) else 0‖^2 := by
    simp only [prob, ket, EuclideanSpace.inner_single_left, map_one, one_mul, state_apply,
      norm_mul, norm_inv, norm_pow, Complex.norm_ofNat, mul_pow]
  have ht (y : Qubits n) : prob (simonRunState x) (j,y) =
      (if dotBits s j = false then ((2:ℝ)^n)⁻¹ ^ 2 * 2 else 0) *
        (Fintype.card {i // x i = y} : ℝ) := by
    rw [hp]
    by_cases hy : ∃ t, x t = y
    · obtain ⟨t,rfl⟩ := hy
      have hsqu : ∀ a : ℂ, ‖sig (dotBits j t) * a‖^2 = ‖a‖^2 := by
        intro a; rw [norm_mul]; have : ‖sig (dotBits j t)‖ = 1 := by simp [sig]; split_ifs <;> norm_num
        rw [this, one_mul]
      have hfcard : (Fintype.card {i // x i = x t} : ℝ) = 2 := by
        have := fiber_sum x s hx hs t (fun _ => (1:ℂ))
        simp only [← Finset.sum_filter] at this
        have hh : (Fintype.card {i // x i = x t} : ℂ) = 2 := by
          simpa [Fintype.card_subtype, one_add_one_eq_two] using this
        exact_mod_cast hh
      rw [fiber_sum x s hx hs, dot_add, sig_add, show ∀ z w : ℂ, z + z*w = z*(1+w) by intros; ring, hc, hsqu, hfcard]
      cases dotBits s j <;> norm_num [sig]
      ring
    · have hz : ∀ i, x i ≠ y := fun i hi => hy ⟨i,hi⟩
      have : IsEmpty {i // x i = y} := ⟨fun i => hy ⟨i,i.property⟩⟩
      simp [hz]
  simp only [marginalFst, ht]
  rw [← Finset.mul_sum, ← Nat.cast_sum, fiber_card_total x]
  have hcard : Fintype.card (Qubits n) = 2^n := by simp [Qubits]
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
  split_ifs <;> field_simp
  simp

private lemma uniform_map_mass {A B : Type*} [Fintype B] [Nonempty B]
    (g : B → A) (hg : Function.Injective g) (a : A) :
    ((PMF.uniformOfFintype B).map g) a =
      if a ∈ Set.range g then (Fintype.card B : ℝ≥0∞)⁻¹ else 0 := by
  classical
  rw [PMF.map_apply]
  by_cases h : a ∈ Set.range g
  · obtain ⟨b,rfl⟩ := h
    simp only [Set.mem_range, hg.eq_iff, PMF.uniformOfFintype_apply]
    simp
  · simp only [Set.mem_range] at h
    simp [h, show ∀ b, a ≠ g b from fun b he => h ⟨b,he.symm⟩]

private lemma iid_uniform_map {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (g : B → A) (hg : Function.Injective g) (k : ℕ) (E : (Fin k → A) → Prop) :
    iidProb ((PMF.uniformOfFintype B).map g) k E =
      (Fintype.card {l : Fin k → B // E (g ∘ l)} : ℝ≥0∞) /
        (Fintype.card (Fin k → B) : ℝ≥0∞) := by
  classical
  let G : (Fin k → B) → (Fin k → A) := fun l => g ∘ l
  have hG : Function.Injective G := by
    intro l r h; funext i; exact hg (congrFun h i)
  rw [iidProb, ← Fintype.sum_of_injective G hG
    (fun l => if E (G l) then (Fintype.card B : ℝ≥0∞)⁻¹ ^ k else 0)
    (fun l => if E l then ∏ i, ((PMF.uniformOfFintype B).map g) (l i) else 0)]
  · simp only [G, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype,
      Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_eq_mul_inv, ENNReal.inv_pow]
  · intro l hl
    have hn : ∃ i, l i ∉ Set.range g := by
      by_contra h
      push Not at h
      apply hl
      choose r hr using h
      exact ⟨r, funext hr⟩
    obtain ⟨i,hi⟩ := hn
    split_ifs
    · apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [uniform_map_mass g hg, hi]
    · rfl
  · intro l
    simp only [G, Function.comp_apply, uniform_map_mass g hg, Set.mem_range_self, if_true,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private lemma iid_le_one {A : Type*} [Fintype A] (μ : PMF A) (k : ℕ)
    (E : (Fin k → A) → Prop) : iidProb μ k E ≤ 1 := by
  classical
  calc
    _ ≤ ∑ l : Fin k → A, ∏ i, μ (l i) := by
      apply Finset.sum_le_sum
      intro l _; split_ifs <;> simp
    _ = ∏ _i : Fin k, ∑ a : A, μ a := (Fintype.prod_sum _).symm
    _ = 1 := by
      have hμ := μ.tsum_coe
      rw [tsum_fintype] at hμ
      simp only [hμ, Finset.prod_const_one]

private lemma iid_mono {A : Type*} [Fintype A] (μ : PMF A) (k : ℕ)
    {E F : (Fin k → A) → Prop} (h : ∀ l, E l → F l) :
    iidProb μ k E ≤ iidProb μ k F := by
  classical
  apply Finset.sum_le_sum
  intro l _
  by_cases he : E l
  · simp [he, h l he]
  · simp [he]

private lemma sample_rank {n m : ℕ} (js : Fin m → Qubits n)
    (s : Fin (n-1) ↪ Fin m)
    (hli : LinearIndependent (ZMod 2) (fun i => simonBitsToZMod2 (js (s i)))) :
    n - 1 ≤ simonSpanRank js := by
  rw [simonSpanRank]
  calc
    _ = finrank (ZMod 2) (span (ZMod 2) (Set.range fun i => simonBitsToZMod2 (js (s i)))) :=
      by simpa only [Fintype.card_fin] using (finrank_span_eq_card hli).symm
    _ ≤ _ := finrank_mono (span_mono (by rintro _ ⟨i,rfl⟩; exact ⟨s i,rfl⟩))

private lemma expected_le {A : Type*} [Fintype A] (μ : PMF A)
    (stop : (k : ℕ) → (Fin k → A) → Prop) (n : ℕ)
    (htail : ∀ t, iidProb μ (n+t) (fun l => ¬ stop (n+t) l) ≤
      (2:ℝ≥0∞)⁻¹ ^ (t+1)) :
    expectedStoppingTime μ stop ≤ n + 1 := by
  classical
  let p : ℕ → ℝ≥0∞ := fun k => iidProb μ k (fun l => ∀ (j : ℕ) (h : j ≤ k), ¬ stop j (fun i => l (Fin.castLE h i)))
  have hp (k : ℕ) : p k ≤ iidProb μ k (fun l => ¬ stop k l) :=
    iid_mono μ k (fun l h => by simpa using h k le_rfl)
  change ∑' k, p k ≤ _
  rw [← (ENNReal.summable (f := fun t => p (t+n))).sum_add_tsum_nat_add']
  calc
    _ ≤ (∑ _k ∈ Finset.range n, (1:ℝ≥0∞)) + ∑' t, (2:ℝ≥0∞)⁻¹ ^ (t+1) := by
      apply add_le_add
      · exact Finset.sum_le_sum fun k _ => iid_le_one μ k _
      · apply ENNReal.tsum_le_tsum
        intro t
        have hcomm := congrArg (fun k => iidProb μ k (fun l => ¬ stop k l)) (Nat.add_comm t n)
        exact (hp (t+n)).trans (hcomm.trans_le (htail t))
    _ = n + 1 := by
      rw [ENNReal.tsum_geometric_add_one]
      norm_num [Finset.sum_const, Finset.card_range]
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private lemma stopping {n : ℕ} (s : Qubits n) (hs : s ≠ 0) :
    ∃ μ : PMF (Qubits n),
      (∀ j, μ j = ENNReal.ofReal (if dotBits s j = false then 2 / (2:ℝ)^n else 0)) ∧
      expectedStoppingTime μ (fun _ l => n - 1 ≤ simonSpanRank l) ≤ (n:ℝ≥0∞) + 1 := by
  classical
  let a := simonBitsToZMod2 s
  have ha : a ≠ 0 := bits_ne_zero hs
  have hn : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst n
    exact hs (Subsingleton.elim _ _)
  let V := {v : Fin n → ZMod 2 // v ⬝ᵥ a = 0}
  let : Nonempty V := ⟨⟨0, by simp⟩⟩
  let g : V → Qubits n := fun v => (bitsEquiv n).symm v.val
  have hg : Function.Injective g := (bitsEquiv n).symm.injective.comp Subtype.val_injective
  have hval (v : V) : simonBitsToZMod2 (g v) = v.val := (bitsEquiv n).apply_symm_apply _
  have hrange (j : Qubits n) : j ∈ Set.range g ↔ dotBits s j = false := by
    constructor
    · rintro ⟨v,rfl⟩
      rw [← dot_zero, dotProduct_comm, hval]
      exact v.property
    · intro h
      have hz : simonBitsToZMod2 j ⬝ᵥ a = 0 :=
        (dot_zero _ _).mpr (by simpa [dotBits, Bool.and_comm] using h)
      exact ⟨⟨simonBitsToZMod2 j,hz⟩, (bitsEquiv n).symm_apply_apply j⟩
  have hcard : Fintype.card V = 2 ^ (n-1) := by
    let e : V ≃ LinearMap.ker (dotMap a) :=
      { toFun := fun v => ⟨v.val,v.property⟩
        invFun := fun v => ⟨v.val,v.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, kernel_dim ha]
  have hcn : (Fintype.card V : ℝ) * 2 = (2:ℝ)^n := by
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, ← pow_succ, Nat.sub_add_cancel hn]
  let μ := (PMF.uniformOfFintype V).map g
  refine ⟨μ, ?_, expected_le μ (fun _ l => n-1 ≤ simonSpanRank l) n ?_⟩
  · intro j
    rw [uniform_map_mass g hg]
    simp only [hrange]
    split_ifs
    · have hr : (Fintype.card V : ℝ)⁻¹ = 2 / (2:ℝ)^n := by
        rw [← hcn]
        field_simp
      have he := congrArg ENNReal.ofReal hr
      simpa only [ENNReal.ofReal_inv_of_pos (by positivity : (0:ℝ) < Fintype.card V),
        ENNReal.ofReal_natCast] using he
    · simp
  · intro t
    rw [iid_uniform_map g hg]
    let good : (Fin (n+t) → V) → Prop := fun l =>
      ∃ e : Fin (n-1) ↪ Fin (n+t), LinearIndependent (ZMod 2) (fun i => (l (e i)).val)
    let bad : (Fin (n+t) → V) → Prop := fun l => ¬(n-1 ≤ simonSpanRank (g ∘ l))
    have hdis : ∀ l, bad l → ¬ good l := by
      intro l hl ⟨e,he⟩
      apply hl
      apply sample_rank (g ∘ l) e
      simpa only [Function.comp_apply, hval] using he
    have hc : Fintype.card {l // bad l} ≤ Fintype.card {l // ¬ good l} :=
      Fintype.card_subtype_mono bad (fun l => ¬ good l) hdis
    have hsum : Fintype.card {l // good l} + Fintype.card {l // ¬ good l} =
        Fintype.card (Fin (n+t) → V) := by
      simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.sumCompl good)
    have hp := QAlgorithms.Nannicini.simon_linearIndependent_prob n t a ha
    change (Fintype.card {l // good l} : ℝ) / (Fintype.card (Fin (n+t) → V) : ℝ) ≥ _ at hp
    have htot : (0:ℝ) < Fintype.card (Fin (n+t) → V) := by positivity
    have hr : (Fintype.card {l // bad l} : ℝ) / (Fintype.card (Fin (n+t) → V) : ℝ) ≤
        1 / (2:ℝ)^(t+1) := by
      have hcR : (Fintype.card {l // bad l} : ℝ) ≤ Fintype.card {l // ¬ good l} := by exact_mod_cast hc
      have hsR : (Fintype.card {l // good l} : ℝ) + Fintype.card {l // ¬ good l} =
          Fintype.card (Fin (n+t) → V) := by exact_mod_cast hsum
      have hp' := (le_div_iff₀ htot).mp hp
      rw [div_le_iff₀ htot]
      nlinarith [hp']
    have he := ENNReal.ofReal_le_ofReal hr
    have hpow : ENNReal.ofReal ((2:ℝ)^(t+1)) = (2:ℝ≥0∞)^(t+1) := by
      norm_cast
    simp only [ENNReal.ofReal_div_of_pos htot, ENNReal.ofReal_natCast] at he
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, hpow,
      one_div, ENNReal.inv_pow] at he
    simpa only [bad, ← Nat.card_eq_fintype_card] using he

theorem solution :
    (∀ (n : ℕ) (x : Qubits n → Qubits n) (s : Qubits n), SimonPromise x s → s ≠ 0 →
      ∀ j : Qubits n, marginalFst (simonRunState x) j =
        if dotBits s j = false then 2 / (2 : ℝ) ^ n else 0) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ (x : Qubits n → Qubits n) (s : Qubits n),
      SimonPromise x s → s ≠ 0 →
      ∃ μ : PMF (Qubits n), (∀ j, μ j = ENNReal.ofReal (marginalFst (simonRunState x) j)) ∧
        expectedStoppingTime μ (fun _ l => n - 1 ≤ simonSpanRank l) ≤
          ENNReal.ofReal (C * n)) ∧
    (∀ (n : ℕ) (s : Qubits n), s ≠ 0 → ∀ (m : ℕ) (js : Fin m → Qubits n),
      (∀ k, dotBits s (js k) = false) → n - 1 ≤ simonSpanRank js →
      ∀ y : Qubits n, y ≠ 0 → (∀ k, dotBits (js k) y = false) → y = s) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ G : BoolCircuit ((n - 1) * n) n,
      G.WellFormed ∧ (G.size : ℝ) ≤ C * (n : ℝ) ^ 3 ∧
      ∀ (s : Qubits n), s ≠ 0 → ∀ js : Fin (n - 1) → Qubits n,
        (∀ k, dotBits s (js k) = false) →
        LinearIndependent (ZMod 2) (fun k => simonBitsToZMod2 (js k)) →
        G.eval (fun p => js (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) = s)  := by
  refine ⟨fun n x s hx hs j => sampling x s hx hs j, ?_, fun n => @unique_mask n, ?_⟩
  · refine ⟨2, by norm_num, 1, ?_⟩
    intro n hn x s _hx hs
    obtain ⟨μ,hμ,he⟩ := stopping s hs
    refine ⟨μ, fun j => ?_, ?_⟩
    · rw [hμ, sampling x s _hx hs]
    · calc
        _ ≤ (n:ℝ≥0∞) + 1 := he
        _ ≤ ENNReal.ofReal (2 * (n:ℝ)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
          have : (1:ℝ≥0∞) ≤ n := by exact_mod_cast hn
          calc
            _ ≤ (n:ℝ≥0∞) + n := add_le_add_right this _
            _ = _ := (two_mul _).symm
  · obtain ⟨C,hC,N,hN⟩ := QAlgorithms.gf2_nullvector_circuit
    refine ⟨C,hC,N,fun n hn => ?_⟩
    obtain ⟨G,hw,hsize,hG⟩ := hN n hn
    refine ⟨G,hw,hsize,fun s hs js hjs hli => ?_⟩
    obtain ⟨hy,hjy⟩ := hG js hli
    exact unique_mask s hs (n-1) js hjs
      (sample_rank js (Function.Embedding.refl _) (by simpa using hli)) _ hy hjy
