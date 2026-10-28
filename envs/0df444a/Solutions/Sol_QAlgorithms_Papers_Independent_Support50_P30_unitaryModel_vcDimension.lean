-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P30.unitaryModel_vcDimension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:28:02.670661+00:00
-- url     : https://prove2.me/submissions/ecbba781-178f-4482-ad50-df4f82aebb38

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30
noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

open QAlgorithms QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50 QAlgorithms.Papers.Independent.Support50.P30

attribute [local instance] LieRing.ofAssociativeRing

theorem vc_range_sum (n : ℕ) :
    ∑ m ∈ Finset.range (n / 2 + 1), (n - 2 * m + 1) ^ 2 = (n + 3).choose 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | k + 2, ih =>
      have h1 : (k + 2) / 2 + 1 = (k / 2 + 1) + 1 := by omega
      rw [h1, Finset.sum_range_succ']
      have h2 : ∀ m ∈ Finset.range (k / 2 + 1), (k + 2 - 2 * (m + 1) + 1) ^ 2 = (k - 2 * m + 1) ^ 2 := by
        intro m _; congr 2; omega
      rw [Finset.sum_congr rfl h2, ih k (by omega)]
      have e1 : (k + 2 + 3).choose 3 = (k + 4).choose 2 + (k + 4).choose 3 := Nat.choose_succ_succ' _ _
      have e2 : (k + 4).choose 3 = (k + 3).choose 2 + (k + 3).choose 3 := Nat.choose_succ_succ' _ _
      have e3 : (k + 4).choose 2 = (k + 3).choose 1 + (k + 3).choose 2 := Nat.choose_succ_succ' _ _
      have e4 := Nat.add_one_mul_choose_eq (k + 2) 1
      simp only [Nat.choose_one_right] at e3 e4
      rw [e1, e2, e3]
      simp only [Nat.mul_zero, Nat.sub_zero]
      nlinarith [e4]

theorem vc_sector_sum (n : ℕ) : (∑ m : Sector n, blockDim n m ^ 2) = (n + 3).choose 3 := by
  rw [← vc_range_sum n, ← Fin.sum_univ_eq_sum_range (fun m => (n - 2 * m + 1) ^ 2)]
  rfl

def vcEq {n : ℕ} (A : QnnOperator n) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) (x y : Qubits n), A (fun j => x (p j)) (fun j => y (p j)) = A x y

theorem vc_perm_iff {n : ℕ} (A : QnnOperator n) : PermutationEquivariant A ↔ vcEq A := by
  have key : ∀ p : Equiv.Perm (Fin n), ∀ x y : Qubits n,
      (A * qubitPermutationMatrix n p) x y = A x (fun j => y (p.symm j)) ∧
      (qubitPermutationMatrix n p * A) x y = A (fun j => x (p j)) y := by
    intro p x y
    constructor
    · simp [Matrix.mul_apply, qubitPermutationMatrix]
    · have : ∀ z : Qubits n, (x = fun j => z (p.symm j)) ↔ z = fun j => x (p j) := by
        intro z; constructor
        · rintro rfl; funext j; simp
        · rintro rfl; funext j; simp
      simp [Matrix.mul_apply, qubitPermutationMatrix, this]
  constructor
  · intro h p x y
    have := congrFun (congrFun (h p) x) (fun j => y (p j))
    rw [(key p x _).1, (key p x _).2] at this
    simpa using this.symm
  · intro h p
    ext x y
    rw [(key p x y).1, (key p x y).2]
    have := h p x (fun j => y (p.symm j))
    simpa using this.symm

theorem vc_collective {n : ℕ} (c : ℂ) (chi : Matrix Bool Bool ℂ) (k : ℕ) :
    vcEq (c • collective n chi k) := by
  intro p x y
  simp only [Matrix.smul_apply, collective, Matrix.sum_apply, pauliString]
  congr 1
  symm
  refine Finset.sum_nbij' (fun s => s.map p.symm.toEmbedding) (fun s => s.map p.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hs ⊢
    simpa using hs
  · intro s hs; simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hs ⊢
    simpa using hs
  · intro s _; ext j; simp
  · intro s _; ext j; simp
  · intro s _
    rw [← Equiv.prod_comp p]
    apply Finset.prod_congr rfl
    intro j _
    simp

theorem vc_mul {n : ℕ} {A B : QnnOperator n} (hA : vcEq A) (hB : vcEq B) : vcEq (A * B) := by
  intro p x y
  simp only [Matrix.mul_apply]
  let e : Qubits n ≃ Qubits n :=
    { toFun := fun w j => w (p j), invFun := fun w j => w (p.symm j),
      left_inv := fun w => by funext j; simp, right_inv := fun w => by funext j; simp }
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro w _
  show A _ (fun j => w (p j)) * B (fun j => w (p j)) _ = _
  rw [hA, hB]

theorem vc_conjTranspose {n : ℕ} {A : QnnOperator n} (hA : vcEq A) : vcEq A.conjTranspose := by
  intro p x y
  simp [Matrix.conjTranspose_apply, hA p y x]

theorem vc_sub {n : ℕ} {A B : QnnOperator n} (hA : vcEq A) (hB : vcEq B) : vcEq (A - B) := by
  intro p x y; simp [hA p x y, hB p x y]

theorem vc_smul {n : ℕ} {A : QnnOperator n} (c : ℂ) (hA : vcEq A) : vcEq (c • A) := by
  intro p x y; simp [hA p x y]

theorem vc_one (n : ℕ) : vcEq (1 : QnnOperator n) := by
  rw [← vc_perm_iff]; intro p; simp

theorem vc_commute {n : ℕ} {A : QnnOperator n} (hA : vcEq A) (p : Equiv.Perm (Fin n)) :
    Commute (qubitPermutationMatrix n p) A :=
  (((vc_perm_iff A).2 hA) p).symm

theorem vc_circuit {n L : ℕ} (word : Fin L → Fin 3) (theta : Fin L → ℝ) :
    vcEq (circuit (fun j => qnnGenerator n (word j)) theta) := by
  rw [← vc_perm_iff]
  intro p
  have hgen : ∀ j : Fin 3, vcEq (qnnGenerator n j) := by
    intro j
    unfold qnnGenerator
    split_ifs
    · exact vc_collective _ _ _
    · exact vc_collective _ _ _
    · exact vc_collective _ _ _
  have : Commute (qubitPermutationMatrix n p) (circuit (fun j => qnnGenerator n (word j)) theta) := by
    unfold circuit orderedProd
    apply Commute.list_prod_right
    intro x hx
    rw [List.mem_reverse, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    unfold qnnLayer
    exact ((vc_commute (hgen (word j)) p).smul_right _).exp_right
  exact this.symm.eq

def vcType {n : ℕ} (q : Qubits n × Qubits n) : Sym (Bool × Bool) n :=
  ⟨Finset.univ.val.map (fun i => (q.1 i, q.2 i)), by simp⟩

theorem vc_orbit {n : ℕ} {q q' : Qubits n × Qubits n} (h : vcType q = vcType q') :
    ∃ p : Equiv.Perm (Fin n), (fun j => q.1 (p j)) = q'.1 ∧ (fun j => q.2 (p j)) = q'.2 := by
  set f : Fin n → Bool × Bool := fun i => (q.1 i, q.2 i)
  set g : Fin n → Bool × Bool := fun i => (q'.1 i, q'.2 i)
  have hm : Finset.univ.val.map f = Finset.univ.val.map g := congrArg Subtype.val h
  have hc : ∀ c, Fintype.card {i // g i = c} = Fintype.card {i // f i = c} := by
    intro c
    have := congrArg (Multiset.count c) hm
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    have e1 : (Multiset.filter (fun i => g i = c) Finset.univ.val) =
        Multiset.filter (fun i => c = g i) Finset.univ.val := by
      congr 1; funext i; simp [eq_comm]
    have e2 : (Multiset.filter (fun i => f i = c) Finset.univ.val) =
        Multiset.filter (fun i => c = f i) Finset.univ.val := by
      congr 1; funext i; simp [eq_comm]
    rw [e1, e2]; exact this.symm
  let e : ∀ c, {i // g i = c} ≃ {i // f i = c} := fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv e, ?_, ?_⟩
  · funext j; have := Equiv.ofFiberEquiv_map e j; exact congrArg Prod.fst this
  · funext j; have := Equiv.ofFiberEquiv_map e j; exact congrArg Prod.snd this

def vcW (n : ℕ) : Submodule ℝ (QnnOperator n) where
  carrier := {A | A.IsHermitian ∧ vcEq A}
  add_mem' := by
    rintro A B ⟨hA, eA⟩ ⟨hB, eB⟩
    refine ⟨hA.add hB, ?_⟩
    intro p x y; simp [eA p x y, eB p x y]
  zero_mem' := ⟨Matrix.isHermitian_zero, by intro p x y; simp⟩
  smul_mem' := by
    rintro r A ⟨hA, eA⟩
    refine ⟨?_, ?_⟩
    · unfold Matrix.IsHermitian at hA ⊢
      rw [Matrix.conjTranspose_smul, hA, star_trivial]
    · intro p x y; simp [eA p x y]

def vcRep {n : ℕ} (κ : Sym (Bool × Bool) n) : Qubits n × Qubits n :=
  if h : ∃ q, vcType q = κ then h.choose else (fun _ => false, fun _ => false)

def vcPsi (n : ℕ) : vcW n →ₗ[ℝ] (Sym (Bool × Bool) n → ℝ) where
  toFun A κ := (A.1 (vcRep κ).1 (vcRep κ).2).re + (A.1 (vcRep κ).1 (vcRep κ).2).im
  map_add' A B := by funext κ; simp; ring
  map_smul' r A := by funext κ; simp; ring

theorem vc_entry {n : ℕ} (A : vcW n) (x y : Qubits n) :
    A.1 x y = A.1 (vcRep (vcType (x, y))).1 (vcRep (vcType (x, y))).2 := by
  have h : ∃ q, vcType q = vcType (x, y) := ⟨_, rfl⟩
  have hr : vcRep (vcType (x, y)) = h.choose := dif_pos h
  have key : ∀ q : Qubits n × Qubits n, vcType q = vcType (x, y) → A.1 x y = A.1 q.1 q.2 := by
    intro q hq
    obtain ⟨p, h1, h2⟩ := vc_orbit hq
    simp only at h1 h2
    subst h1 h2
    exact A.2.2 p _ _
  rw [hr]
  exact key _ h.choose_spec

theorem vc_psi_inj (n : ℕ) : Function.Injective (vcPsi n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro A hA
  have h0 : ∀ x y : Qubits n, (A.1 x y).re + (A.1 x y).im = 0 := by
    intro x y
    have := congrFun hA (vcType (x, y))
    rw [vc_entry A x y]
    simpa [vcPsi] using this
  apply Subtype.ext
  ext x y
  have h1 := h0 x y
  have h2 := h0 y x
  have hh : A.1 y x = star (A.1 x y) := (A.2.1.apply y x).symm
  rw [hh] at h2
  simp at h2
  apply Complex.ext <;> simp <;> linarith

theorem vc_finrank (n : ℕ) : Module.finrank ℝ (vcW n) ≤ (n + 3).choose 3 := by
  have := LinearMap.finrank_le_finrank_of_injective (vc_psi_inj n)
  rw [Module.finrank_fintype_fun_eq_card, Sym.card_sym_eq_multichoose, Nat.multichoose_eq] at this
  simp only [Fintype.card_prod, Fintype.card_bool] at this
  have e : (2 * 2 + n - 1).choose n = (n + 3).choose 3 := by
    rw [show 2 * 2 + n - 1 = n + 3 by omega, Nat.choose_symm_add]
  omega

theorem vc_general {X V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ℓ : X → V →ₗ[ℝ] ℝ) (C : Set (X → Bool))
    (hC : ∀ h ∈ C, ∃ A : V, ∀ x, h x = decide (0 ≤ ℓ x A)) :
    QAlgorithms.Learning.vcDimSet C ≤ (Module.finrank ℝ V : ℕ∞) := by
  refine iSup₂_le fun s hs => ?_
  by_contra hlt
  have hlt' : Module.finrank ℝ V < s.card := by exact_mod_cast not_le.mp hlt
  have hni : ¬ LinearIndependent ℝ (fun x : s => ℓ x) := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Subspace.dual_finrank_eq, Fintype.card_coe] at this
    omega
  rw [Fintype.not_linearIndependent_iff] at hni
  obtain ⟨g, hsum, i, hi⟩ := hni
  obtain ⟨g', hsum', i', hi'⟩ : ∃ g' : s → ℝ, (∑ x, g' x • ℓ x) = 0 ∧ ∃ i, 0 < g' i := by
    rcases lt_or_gt_of_ne hi with h | h
    · refine ⟨fun x => -g x, ?_, i, by simp; linarith⟩
      show ∑ x, (-g x) • ℓ x = 0
      rw [Finset.sum_congr rfl (fun x _ => neg_smul (g x) (ℓ x)), Finset.sum_neg_distrib, hsum, neg_zero]
    · exact ⟨g, hsum, i, h⟩
  obtain ⟨h, hh, hy⟩ := hs (fun x => decide (g' x ≤ 0))
  obtain ⟨A, hA⟩ := hC h hh
  have hz : ∑ x : s, g' x * ℓ x A = 0 := by
    have := congrArg (fun f : V →ₗ[ℝ] ℝ => f A) hsum'
    simpa using this
  have hterm : ∀ x : s, g' x * ℓ x A ≤ 0 := by
    intro x
    have e := hy x
    rw [hA] at e
    by_cases hx : g' x ≤ 0
    · have : 0 ≤ ℓ x A := by simpa [hx] using e
      exact mul_nonpos_of_nonpos_of_nonneg hx this
    · have : ℓ x A < 0 := by simpa [hx] using e
      exact (mul_neg_of_pos_of_neg (lt_of_not_ge hx) this).le
  have hlt2 : ∑ x : s, g' x * ℓ x A < ∑ x : s, (0 : ℝ) := by
    apply Finset.sum_lt_sum (fun x _ => hterm x)
    refine ⟨i', Finset.mem_univ _, ?_⟩
    have e := hy i'
    rw [hA] at e
    have hx : ¬ g' i' ≤ 0 := not_le.mpr hi'
    have : ℓ i' A < 0 := by simpa [hx] using e
    exact mul_neg_of_pos_of_neg hi' this
  rw [Finset.sum_const_zero, hz] at hlt2; exact lt_irrefl _ hlt2

def vcEll {n : ℕ} (ρ : QnnDensity n) : vcW n →ₗ[ℝ] ℝ where
  toFun A := (ρ.1 * A.1).trace.re
  map_add' A B := by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' r A := by
    simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
    rw [Matrix.mul_smul, Matrix.trace_smul]
    simp

theorem vc_O {n : ℕ} {O : QnnOperator n} (hO : O ∈ qnnMeasurementFamily n) : vcEq O := by
  obtain ⟨chi, _, h | h | h⟩ := hO
  · rw [h]; exact vc_collective _ _ _
  · rw [h]; exact vc_collective _ _ _
  · rw [h, ← one_smul ℂ (collective n chi n)]; exact vc_collective _ _ _

theorem solution {n L : ℕ} (hn : 2 ≤ n) (word : Fin L → Fin 3)
    (O : QnnOperator n) (hO : O ∈ qnnMeasurementFamily n) (hHerm : O.IsHermitian) (b : ℝ) :
    QAlgorithms.Learning.vcDimSet (classifierFamily word O b) ≤
      ((∑ m : Sector n, blockDim n m ^ 2 : ℕ) : ℕ∞) ∧
    (∑ m : Sector n, blockDim n m ^ 2) = (n + 3).choose 3 := by
  refine ⟨?_, vc_sector_sum n⟩
  rw [vc_sector_sum n]
  refine le_trans (vc_general (fun ρ => vcEll ρ) _ ?_) (by exact_mod_cast vc_finrank n)
  rintro h ⟨theta, rfl⟩
  set U := circuit (fun j => qnnGenerator n (word j)) theta with hU
  have hUe : vcEq U := vc_circuit word theta
  let W : vcW n := ⟨U.conjTranspose * O * U,
    Matrix.isHermitian_conjTranspose_mul_mul U hHerm,
    vc_mul (vc_mul (vc_conjTranspose hUe) (vc_O hO)) hUe⟩
  let I1 : vcW n := ⟨1, Matrix.isHermitian_one, vc_one n⟩
  refine ⟨W - b • I1, fun ρ => ?_⟩
  have hloss : qnnLoss U ρ.1 O = (ρ.1 * (U.conjTranspose * O * U)).trace.re := by
    unfold qnnLoss
    rw [show U * ρ.1 * U.conjTranspose * O = U * (ρ.1 * U.conjTranspose * O) by
      simp [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  have hl : vcEll ρ (W - b • I1) = qnnLoss U ρ.1 O - b := by
    rw [map_sub, map_smul, hloss]
    simp [vcEll, W, I1, ρ.2.2]
  rw [hl]; simp only [sub_nonneg]; rfl


end
