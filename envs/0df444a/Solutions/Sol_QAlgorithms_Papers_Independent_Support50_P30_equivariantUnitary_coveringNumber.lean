-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P30.equivariantUnitary_coveringNumber
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:58:21.142971+00:00
-- url     : https://prove2.me/submissions/7dabe0db-e6e9-4bd3-bb52-ecc8886e7d5b

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P30 Metric Set

namespace P30Cover

/-! ### Volumetric packing bound in a finite-dimensional real normed space -/

theorem finset_card_le_of_separated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (ε : ℝ) (hε : 0 < ε) (t : Finset E) (ht : ∀ x ∈ t, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ε < dist x y) :
    (t.card : ℝ) ≤ (1 + 2 / ε) ^ Module.finrank ℝ E := by
  set D := Module.finrank ℝ E
  let μ : Measure E := Measure.addHaar
  have hm0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hmtop : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hdisj : (↑t : Set E).PairwiseDisjoint (fun x => ball x (ε / 2)) := by
    intro x hx y hy hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hzx hzy
    have h1 := hsep x hx y hy hxy
    rw [mem_ball] at hzx hzy
    have := dist_triangle x z y
    rw [dist_comm z x] at hzx
    linarith
  have hsub : (⋃ x ∈ t, ball x (ε / 2)) ⊆ ball 0 (1 + ε / 2) := by
    intro z hz
    simp only [mem_iUnion, exists_prop] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    rw [mem_ball, dist_zero_right]
    rw [mem_ball, dist_eq_norm] at hzx
    have := norm_le_norm_add_norm_sub' z x
    have := ht x hx
    have h3 : ‖z - x‖ = ‖x - z‖ := norm_sub_rev z x
    linarith
  have hunion : μ (⋃ x ∈ t, ball x (ε / 2)) =
      (t.card : ℝ≥0∞) * (ENNReal.ofReal ((ε / 2) ^ D) * μ (ball 0 1)) := by
    rw [measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)]
    simp_rw [Measure.addHaar_ball_of_pos μ _ (by positivity : (0:ℝ) < ε / 2)]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hbig : μ (ball 0 (1 + ε / 2)) = ENNReal.ofReal ((1 + ε / 2) ^ D) * μ (ball 0 1) :=
    Measure.addHaar_ball_of_pos μ _ (by positivity)
  have hle : (t.card : ℝ≥0∞) * ENNReal.ofReal ((ε / 2) ^ D) * μ (ball 0 1) ≤
      ENNReal.ofReal ((1 + ε / 2) ^ D) * μ (ball 0 1) := by
    rw [mul_assoc, ← hunion, ← hbig]
    exact measure_mono hsub
  rw [mul_comm _ (μ (ball 0 1)), mul_comm _ (μ (ball 0 1)),
    ENNReal.mul_le_mul_iff_right hm0 hmtop] at hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hpos : (0:ℝ) < (ε / 2) ^ D := by positivity
  rw [← le_div_iff₀ hpos] at hle
  calc (t.card : ℝ) ≤ (1 + ε / 2) ^ D / (ε / 2) ^ D := hle
    _ = ((1 + ε / 2) / (ε / 2)) ^ D := by rw [← div_pow]
    _ = (1 + 2 / ε) ^ D := by
        congr 1
        field_simp
        ring

theorem encard_le_of_separated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (ε : ℝ) (hε : 0 < ε) (C : Set E) (hC : ∀ x ∈ C, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε < dist x y) :
    C.encard ≤ (Nat.floor ((1 + 2 / ε) ^ Module.finrank ℝ E) : ℕ∞) := by
  set D := Module.finrank ℝ E
  have key : ∀ t : Finset E, ↑t ⊆ C → (t.card : ℝ) ≤ (1 + 2 / ε) ^ D := fun t hts =>
    finset_card_le_of_separated ε hε t (fun x hx => hC x (hts hx))
      (fun x hx y hy hxy => hsep x (hts hx) y (hts hy) hxy)
  have hfin : C.Finite := by
    by_contra hinf
    obtain ⟨t, hts, htc⟩ := (Set.Infinite.exists_subset_card_eq hinf
      (Nat.floor ((1 + 2 / ε) ^ D) + 1))
    have h1 := key t hts
    rw [htc] at h1
    have h2 := Nat.lt_floor_add_one ((1 + 2 / ε) ^ D)
    push_cast at h1
    linarith
  rw [hfin.encard_eq_coe_toFinset_card]
  have := key hfin.toFinset (by simp)
  exact_mod_cast Nat.le_floor this

/-! ### Permutations from equal multisets -/

theorem exists_perm_of_map_eq {n : ℕ} {α : Type*} [DecidableEq α] (f g : Fin n → α)
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j, f j = g (σ j) := by
  have hc : ∀ a, Fintype.card {j // f j = a} = Fintype.card {j // g j = a} := by
    intro a
    have := congrArg (Multiset.count a) h
    rw [Multiset.count_map, Multiset.count_map, ← Finset.filter_val, ← Finset.filter_val,
      Finset.card_val, Finset.card_val] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [eq_comm] at this ⊢
    exact this
  let e : (Σ a, {j // f j = a}) ≃ (Σ a, {j // g j = a}) :=
    Equiv.sigmaCongrRight (fun a => Fintype.equivOfCardEq (hc a))
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans (e.trans (Equiv.sigmaFiberEquiv g)),
    fun j => ?_⟩
  simp only [Equiv.trans_apply, Equiv.sigmaFiberEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, e,
    Equiv.sigmaCongrRight_apply]
  exact ((Fintype.equivOfCardEq (hc (f j))) ⟨j, rfl⟩).2.symm

/-! ### The commutant as a real subspace -/

theorem mul_perm_apply {n : ℕ} (A : QnnOperator n) (p : Equiv.Perm (Fin n)) (x y : Qubits n) :
    (A * qubitPermutationMatrix n p) x y = A x (fun j => y (p.symm j)) := by
  simp [Matrix.mul_apply, qubitPermutationMatrix, Finset.sum_ite_eq']

theorem perm_mul_apply {n : ℕ} (A : QnnOperator n) (p : Equiv.Perm (Fin n)) (x y : Qubits n) :
    (qubitPermutationMatrix n p * A) x y = A (fun j => x (p j)) y := by
  have hiff : ∀ z : Qubits n, (x = fun j => z (p.symm j)) ↔ z = fun j => x (p j) := by
    intro z
    constructor
    · intro h
      funext j
      have := congrFun h (p j)
      simpa using this.symm
    · intro h
      subst h
      funext j
      simp
  simp only [Matrix.mul_apply, qubitPermutationMatrix]
  simp_rw [hiff]
  simp [Finset.sum_ite_eq']

theorem equivariant_perm {n : ℕ} {A : QnnOperator n} (hA : PermutationEquivariant A)
    (p : Equiv.Perm (Fin n)) (x y : Qubits n) :
    A (fun j => x (p j)) (fun j => y (p j)) = A x y := by
  have := congrFun (congrFun (hA p) x) (fun j => y (p j))
  rw [mul_perm_apply, perm_mul_apply] at this
  rw [← this]
  congr 1
  funext j
  simp

def commutantSub (n : ℕ) : Submodule ℝ (QnnOperator n) where
  carrier := {A | PermutationEquivariant A}
  add_mem' := by
    intro A B hA hB p
    rw [add_mul, mul_add, hA p, hB p]
  zero_mem' := by
    intro p
    simp
  smul_mem' := by
    intro r A hA p
    rw [Matrix.smul_mul, Matrix.mul_smul, hA p]

def prof {n : ℕ} (xy : Qubits n × Qubits n) : Sym (Bool × Bool) n :=
  ⟨Multiset.map (fun j => (xy.1 j, xy.2 j)) Finset.univ.val, by simp⟩

def rep {n : ℕ} (s : Sym (Bool × Bool) n) : Qubits n × Qubits n :=
  if h : ∃ xy : Qubits n × Qubits n, prof xy = s then h.choose else default

theorem prof_rep {n : ℕ} (xy : Qubits n × Qubits n) : prof (rep (prof xy)) = prof xy := by
  have h : ∃ xy' : Qubits n × Qubits n, prof xy' = prof xy := ⟨xy, rfl⟩
  simp only [rep, dif_pos h]
  exact h.choose_spec

def Phi (n : ℕ) : commutantSub n →ₗ[ℝ] (Sym (Bool × Bool) n → ℂ) where
  toFun A := fun s => A.val (rep s).1 (rep s).2
  map_add' := by
    intro A B
    funext s
    simp
  map_smul' := by
    intro r A
    funext s
    simp

theorem Phi_injective (n : ℕ) : Function.Injective (Phi n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro A hA
  apply Subtype.ext
  show A.val = 0
  ext x y
  rw [Matrix.zero_apply]
  have h0 : A.val (rep (prof (x, y))).1 (rep (prof (x, y))).2 = 0 := by
    have := congrFun hA (prof (x, y))
    simpa [Phi] using this
  have hp : Multiset.map (fun j => ((rep (prof (x, y))).1 j, (rep (prof (x, y))).2 j))
      Finset.univ.val = Multiset.map (fun j => (x j, y j)) Finset.univ.val :=
    congrArg Subtype.val (prof_rep (x, y))
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq (fun j => (x j, y j))
    (fun j => ((rep (prof (x, y))).1 j, (rep (prof (x, y))).2 j)) hp.symm
  set R := rep (prof (x, y)) with hR
  have key := equivariant_perm A.2 σ R.1 R.2
  have hx : (fun j => R.1 (σ j)) = x := by
    funext j
    exact (congrArg Prod.fst (hσ j)).symm
  have hy : (fun j => R.2 (σ j)) = y := by
    funext j
    exact (congrArg Prod.snd (hσ j)).symm
  rw [hx, hy] at key
  rw [key]
  exact h0

theorem finrank_commutant_le (n : ℕ) :
    Module.finrank ℝ (commutantSub n) ≤ 2 * (n + 3).choose 3 := by
  have h := LinearMap.finrank_le_finrank_of_injective (Phi_injective n)
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Complex.finrank_real_complex,
    Sym.card_sym_eq_choose, Fintype.card_prod, Fintype.card_bool] at h
  have h2 : (2 * 2 + n - 1).choose n = (n + 3).choose 3 := by
    rw [show 2 * 2 + n - 1 = n + 3 by omega, Nat.choose_symm_add]
  rw [h2] at h
  simpa [mul_comm] using h

/-! ### The covering-number bound -/

theorem unitaryFamily_coveringNumber (n : ℕ) (epsilon : ℝ≥0)
    (hpos : 0 < epsilon) (hsmall : epsilon ≤ 1) :
    (Metric.coveringNumber epsilon (unitaryFamily n) : ℝ≥0∞) ≤
      ENNReal.ofReal ((6 / (epsilon : ℝ)) ^ (2 * (n + 3).choose 3)) := by
  let W := commutantSub n
  let _i : MeasurableSpace W := borel W
  have _i2 : BorelSpace W := ⟨rfl⟩
  let A' : Set W := {U | U.val ∈ unitaryFamily n}
  have himage : Subtype.val '' A' = unitaryFamily n := by
    ext U
    constructor
    · rintro ⟨V, hV, rfl⟩
      exact hV
    · intro hU
      exact ⟨⟨U, hU.2⟩, hU, rfl⟩
  have hiso : Isometry (Subtype.val : W → QnnOperator n) := isometry_subtype_coe
  have hε : (0 : ℝ) < epsilon := hpos
  set D := Module.finrank ℝ W
  have hpack : ∀ C : Set W, C ⊆ A' → IsSeparated (epsilon : ℝ≥0∞) C →
      C.encard ≤ (Nat.floor ((1 + 2 / (epsilon : ℝ)) ^ D) : ℕ∞) := by
    intro C hCA hCsep
    apply encard_le_of_separated (epsilon : ℝ) hε C
    · intro x hx
      have hx' : x.val ∈ unitaryFamily n := hCA hx
      rw [Submodule.coe_norm]
      exact (CStarRing.norm_of_mem_unitary hx'.1).le
    · intro x hx y hy hxy
      have := hCsep hx hy hxy
      change (epsilon : ℝ≥0∞) < edist x y at this
      rw [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nndist] at this
      exact this
  have hpackN : Metric.packingNumber epsilon A' ≤ (Nat.floor ((1 + 2 / (epsilon : ℝ)) ^ D) : ℕ∞) := by
    simp only [Metric.packingNumber, iSup_le_iff]
    exact hpack
  calc (Metric.coveringNumber epsilon (unitaryFamily n) : ℝ≥0∞)
      = (Metric.coveringNumber epsilon A' : ℝ≥0∞) := by
        rw [← himage, hiso.coveringNumber_image]
    _ ≤ (Metric.packingNumber epsilon A' : ℝ≥0∞) :=
        ENat.toENNReal_le.mpr (Metric.coveringNumber_le_packingNumber _ _)
    _ ≤ ((Nat.floor ((1 + 2 / (epsilon : ℝ)) ^ D) : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.mpr hpackN
    _ = ENNReal.ofReal (Nat.floor ((1 + 2 / (epsilon : ℝ)) ^ D) : ℕ) := by
        rw [ENat.toENNReal_coe, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((6 / (epsilon : ℝ)) ^ (2 * (n + 3).choose 3)) := by
        apply ENNReal.ofReal_le_ofReal
        have hD : D ≤ 2 * (n + 3).choose 3 := finrank_commutant_le n
        have h1 : (1 + 2 / (epsilon : ℝ)) ^ D ≤ (6 / (epsilon : ℝ)) ^ D := by
          apply pow_le_pow_left₀ (by positivity)
          have : (1 : ℝ) ≤ 1 / (epsilon : ℝ) := by
            rw [le_div_iff₀ hε]
            simpa using hsmall
          have h6 : (6 : ℝ) / epsilon = 1 / epsilon + 1 / epsilon + 4 / epsilon := by ring
          have h2 : (2 : ℝ) / epsilon = 2 * (1 / epsilon) := by ring
          rw [h6, h2]
          have h4 : (4 : ℝ) / epsilon = 4 * (1 / epsilon) := by ring
          rw [h4]
          linarith
        have h2 : (6 / (epsilon : ℝ)) ^ D ≤ (6 / (epsilon : ℝ)) ^ (2 * (n + 3).choose 3) := by
          apply pow_le_pow_right₀ _ hD
          rw [le_div_iff₀ hε]
          have : (epsilon : ℝ) ≤ 1 := hsmall
          linarith
        calc ((Nat.floor ((1 + 2 / (epsilon : ℝ)) ^ D) : ℕ) : ℝ)
            ≤ (1 + 2 / (epsilon : ℝ)) ^ D := Nat.floor_le (by positivity)
          _ ≤ _ := h1.trans h2

end P30Cover

theorem solution (n : ℕ) (epsilon : ℝ≥0)
    (hpos : 0 < epsilon) (hsmall : epsilon ≤ 1) :
    (Metric.coveringNumber epsilon (unitaryFamily n) : ℝ≥0∞) ≤
      ENNReal.ofReal ((6 / (epsilon : ℝ)) ^ (2 * (n + 3).choose 3)) :=
  P30Cover.unitaryFamily_coveringNumber n epsilon hpos hsmall

end
