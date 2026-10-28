-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.boolean_face_charge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:25:34.249543+00:00
-- url     : https://prove2.me/submissions/b51fbbea-4225-42d3-a8d9-b8cda9542326

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62
namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

theorem S200B_list_split (l : List ℕ) (hl : l.Pairwise (· ≤ ·)) (q : ℕ) (hq1 : 1 ≤ q)
    (hq2 : q ≤ l.length) : ∃ m, (∀ v ∈ l.take q, v ≤ m) ∧ ∀ v ∈ l.drop q, m ≤ v := by
  rw [List.pairwise_iff_getElem] at hl
  refine ⟨l[q-1]'(by omega), ?_, ?_⟩
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
    rw [List.getElem_take]
    simp only [List.length_take] at hi
    rcases Nat.lt_or_ge i (q-1) with h | h
    · exact hl _ _ _ _ h
    · have : i = q - 1 := by omega
      subst this; exact le_rfl
  · intro v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
    rw [List.getElem_drop]
    simp only [List.length_drop] at hj
    exact hl _ _ _ _ (by omega)

theorem S200B_charge_eq (n q : ℕ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2 ^ n) :
    ∃ m : ℕ, (charge n q : ℝ) = q * (2:ℝ) ^ m -
      ∑ x : Qubits n, max ((2:ℝ) ^ m - 2 ^ (hammingWeight x)) 0 := by
  set g : Fin (2 ^ n) → ℕ := fun x => hammingWeight (natToBits n x.val) with hg
  set l := (List.ofFn g).mergeSort (fun a b => decide (a ≤ b)) with hl
  have hsort : l.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) _
  have hperm : l.Perm (List.ofFn g) := List.mergeSort_perm _ _
  have hlen : l.length = 2 ^ n := by rw [hperm.length_eq, List.length_ofFn]
  obtain ⟨m, hm1, hm2⟩ := S200B_list_split l hsort q hq1 (by omega)
  refine ⟨m, ?_⟩
  set h : ℕ → ℝ := fun w => max ((2:ℝ) ^ m - 2 ^ w) 0 with hh
  have hsum : ∑ x : Qubits n, h (hammingWeight x) = (l.map h).sum := by
    rw [(hperm.map h).sum_eq, List.map_ofFn, List.sum_ofFn]
    refine (Fintype.sum_equiv (bitsEquivFin n) _ _ ?_)
    intro x
    simp only [Function.comp, hg, natToBits]
    congr 3
    apply (bitsEquivFin n).injective
    simp only [Equiv.apply_symm_apply]
    ext; simp [Nat.mod_eq_of_lt ((bitsEquivFin n) x).isLt]
  have hcharge : (charge n q : ℝ) = ((l.take q).map (fun w => (2:ℝ) ^ w)).sum := by
    simp only [charge, Nat.cast_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro v _
    simp
  have hsplit : (l.map h).sum = ((l.take q).map h).sum + ((l.drop q).map h).sum := by
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  have hdrop : ((l.drop q).map h).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    simp only [hh]
    apply max_eq_right
    have := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (hm2 v hv)
    linarith
  have htake : ((l.take q).map (fun w => (2:ℝ) ^ w)).sum + ((l.take q).map h).sum
      = q * (2:ℝ) ^ m := by
    rw [← List.sum_map_add]
    rw [List.map_congr_left (g := fun _ => (2:ℝ) ^ m)]
    · rw [List.map_const', List.sum_replicate, List.length_take, nsmul_eq_mul]
      congr 2; omega
    · intro v hv
      simp only [hh]
      have := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (hm1 v hv)
      rw [max_eq_left (by linarith)]; ring
  rw [hsum, hcharge, hsplit, hdrop]
  linarith



theorem S200B_hinge (a b c θ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c) (hca : c ≤ a)
    (hcb : c ≤ b) (hθ : 0 ≤ θ) :
    max (a - θ) 0 + max (2 * c - θ) 0 + max (b - θ) 0 ≤
      max (a + b - θ) 0 + max (a + b - 2 * θ) 0 := by
  rcases le_total a b with hab | hab <;>
  rcases le_total (a - θ) 0 with h1 | h1 <;> rcases le_total (2*c - θ) 0 with h2 | h2 <;>
  rcases le_total (b - θ) 0 with h3 | h3 <;> rcases le_total (a + b - θ) 0 with h4 | h4 <;>
  rcases le_total (a + b - 2*θ) 0 with h5 | h5 <;>
  simp only [max_eq_left, max_eq_right, h1, h2, h3, h4, h5] <;> linarith

theorem S200B_sum_qubits {M : Type*} [AddCommMonoid M] (n : ℕ) (f : Qubits (n+1) → M) :
    ∑ x, f x = ∑ x : Qubits n, f (Fin.cons false x) + ∑ x : Qubits n, f (Fin.cons true x) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    add_comm]
  rfl

theorem S200B_sum_faces {M : Type*} [AddCommMonoid M] (n : ℕ) (f : (Fin (n+1) → Fin 3) → M) :
    ∑ F, f F = ∑ F : Fin n → Fin 3,
      (f (Fin.cons 0 F) + f (Fin.cons 1 F) + f (Fin.cons 2 F)) := by
  rw [← (Fin.consEquiv (fun _ => Fin 3)).sum_comp, Fintype.sum_prod_type, Fin.sum_univ_three,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  rfl

theorem S200B_hw_cons (n : ℕ) (b : Bool) (x : Qubits n) :
    hammingWeight (Fin.cons b x : Qubits (n+1)) = hammingWeight x + (if b then 1 else 0) := by
  unfold hammingWeight
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  cases b <;> simp [add_comm]

theorem S200B_card_eq_sum {α : Type*} [Fintype α] (s : Finset α) :
    s.card = ∑ x, if x ∈ s then 1 else 0 := by
  rw [Finset.sum_boole]; congr 1; ext; simp

def S200B_P (c : Fin 3) (b : Bool) : Prop :=
  c.val = 1 ∨ (c.val = 0 ∧ b = false) ∨ (c.val = 2 ∧ b = true)

theorem S200B_mem_cons (n : ℕ) (c : Fin 3) (F : Fin n → Fin 3) (b : Bool) (y : Qubits n) :
    (Fin.cons b y : Qubits (n+1)) ∈ faceVertices (Fin.cons c F : Fin (n+1) → Fin 3) ↔
      S200B_P c b ∧ y ∈ faceVertices F := by
  simp only [faceVertices, Finset.mem_filter, Finset.mem_univ, true_and, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, S200B_P]

theorem S200B_card_cons (n : ℕ) (c : Fin 3) (F : Fin n → Fin 3) :
    ((faceVertices (Fin.cons c F : Fin (n+1) → Fin 3)).card : ℝ) =
      ((if S200B_P c false then 1 else 0) + (if S200B_P c true then 1 else 0)) *
        (faceVertices F).card := by
  rw [S200B_card_eq_sum, S200B_sum_qubits, S200B_card_eq_sum]
  simp only [S200B_mem_cons]
  push_cast
  rw [add_mul, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> split_ifs <;> simp_all

def S200B_half {n : ℕ} (Y : Finset (Qubits (n+1))) (b : Bool) : Finset (Qubits n) :=
  univ.filter (fun x => (Fin.cons b x : Qubits (n+1)) ∈ Y)

theorem S200B_subset_cons (n : ℕ) (c : Fin 3) (F : Fin n → Fin 3) (Y : Finset (Qubits (n+1))) :
    faceVertices (Fin.cons c F : Fin (n+1) → Fin 3) ⊆ Y ↔
      (S200B_P c false → faceVertices F ⊆ S200B_half Y false) ∧
      (S200B_P c true → faceVertices F ⊆ S200B_half Y true) := by
  simp only [Finset.subset_iff, Fin.forall_fin_succ_pi (P := fun y => y ∈ _ → y ∈ Y),
    S200B_mem_cons, S200B_half, Finset.mem_filter, Finset.mem_univ, true_and, Bool.forall_bool]
  tauto

theorem S200B_card_half (n : ℕ) (Y : Finset (Qubits (n+1))) :
    Y.card = (S200B_half Y false).card + (S200B_half Y true).card := by
  rw [S200B_card_eq_sum Y, S200B_sum_qubits]
  simp only [S200B_half, Finset.card_filter]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> congr

def S200B_L {n : ℕ} (Y : Finset (Qubits n)) (μ : ℝ) : ℝ :=
  ∑ F : Fin n → Fin 3, if faceVertices F ⊆ Y then max (μ * (faceVertices F).card - 1) 0 else 0

def S200B_R (n : ℕ) (t : ℝ) : ℝ := ∑ x : Qubits n, max (t - 2 ^ hammingWeight x) 0

theorem S200B_L_succ (n : ℕ) (Y : Finset (Qubits (n+1))) (μ : ℝ) :
    S200B_L Y μ = S200B_L (S200B_half Y false) μ +
      S200B_L (S200B_half Y false ∩ S200B_half Y true) (2 * μ) +
      S200B_L (S200B_half Y true) μ := by
  unfold S200B_L
  rw [S200B_sum_faces, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro F _
  simp only [S200B_subset_cons, S200B_card_cons, S200B_P, Finset.subset_inter_iff]
  simp
  congr 2
  ring

theorem S200B_R_succ (n : ℕ) (t : ℝ) :
    S200B_R (n+1) t = ∑ x : Qubits n,
      (max (t - 2 ^ hammingWeight x) 0 + max (t - 2 * 2 ^ hammingWeight x) 0) := by
  unfold S200B_R
  rw [S200B_sum_qubits, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp [S200B_hw_cons, pow_succ, mul_comm]

theorem S200B_G (n : ℕ) : ∀ (Y : Finset (Qubits n)) (μ : ℝ), 0 ≤ μ →
    S200B_L Y μ ≤ S200B_R n (μ * Y.card) := by
  induction n with
  | zero =>
    intro Y μ hμ
    unfold S200B_L S200B_R
    rw [Fintype.sum_unique, Fintype.sum_unique]
    have hfv : ∀ F : Fin 0 → Fin 3, faceVertices F = univ := by
      intro F; ext y; simp [faceVertices]
    simp only [hfv]
    split_ifs with h
    · have : Y = univ := Finset.eq_univ_of_forall (fun x => h (Finset.mem_univ x))
      subst this
      simp [hammingWeight]
    · exact le_max_right _ _
  | succ n ih =>
    intro Y μ hμ
    rw [S200B_L_succ, S200B_R_succ, S200B_card_half]
    set A := S200B_half Y false
    set B := S200B_half Y true
    have h1 := ih A μ hμ
    have h2 := ih (A ∩ B) (2 * μ) (by linarith)
    have h3 := ih B μ hμ
    refine le_trans (add_le_add (add_le_add h1 h2) h3) ?_
    unfold S200B_R
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    have hA : ((A ∩ B).card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card Finset.inter_subset_left
    have hB : ((A ∩ B).card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    have := S200B_hinge (μ * A.card) (μ * B.card) (μ * (A ∩ B).card) (2 ^ hammingWeight x)
      (by positivity) (by positivity) (by positivity) (mul_le_mul_of_nonneg_left hA hμ)
      (mul_le_mul_of_nonneg_left hB hμ) (by positivity)
    push_cast
    calc _ = max (μ * A.card - 2 ^ hammingWeight x) 0 +
          max (2 * (μ * (A ∩ B).card) - 2 ^ hammingWeight x) 0 +
          max (μ * B.card - 2 ^ hammingWeight x) 0 := by ring_nf
      _ ≤ _ := this
      _ = _ := by ring_nf

theorem S200B_term (k μ : ℝ) (hk : 0 < k) : μ - k⁻¹ * max (μ * k - 1) 0 ≤ k⁻¹ := by
  have h1 : k⁻¹ * (μ * k - 1) ≤ k⁻¹ * max (μ * k - 1) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (inv_nonneg.mpr hk.le)
  have h2 : k⁻¹ * (μ * k - 1) = μ - k⁻¹ := by field_simp
  linarith

theorem S200B_clause1 (n q : ℕ) (Y : Finset (Qubits n)) (y0 : Qubits n) (_hy0 : y0 ∈ Y)
    (hfaces : q ≤ (univ.filter (fun F : Fin n → Fin 3 => y0 ∈ faceVertices F ∧ faceVertices F ⊆ Y)).card) :
    q ≤ Y.card := by
  refine le_trans hfaces ?_
  apply Finset.card_le_card_of_injOn (fun F i => if (F i).val = 1 then !(y0 i) else y0 i)
  · intro F hF
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hF
    apply hF.2
    have hy := hF.1
    simp only [faceVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    intro i
    rcases hy i with h | ⟨h, h'⟩ | ⟨h, h'⟩
    · simp [h]
    · simp [h, h']
    · simp [h, h']
  · intro F hF G hG heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hF hG
    have hF1 := hF.1
    have hG1 := hG.1
    simp only [faceVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hF1 hG1
    funext i
    have hi := congr_fun heq i
    simp only at hi
    apply Fin.ext
    rcases hF1 i with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hG1 i with g1 | ⟨g1, g2⟩ | ⟨g1, g2⟩ <;>
      simp_all

/-- arXiv:2609.40054v1, PDF pp.50, 58, 59, 60, Lemma 5.6: Boolean cube face incidence charge. -/
theorem S200B_main (n q : ℕ) (hq : 0 < q) (Y : Finset (Qubits n)) (hY : Y.Nonempty)
    (hfaces : ∀ y ∈ Y, q ≤ (univ.filter (fun F : Fin n → Fin 3 => y ∈ faceVertices F ∧ faceVertices F ⊆ Y)).card) :
    q ≤ Y.card ∧ Y.card ≤ 2 ^ n ∧
    ∀ F : Qubits n → Finset (Fin n → Fin 3),
      (∀ y ∈ Y, (F y).card = q ∧ ∀ f ∈ F y, y ∈ faceVertices f ∧ faceVertices f ⊆ Y) →
      (charge n q : ℝ) ≤ ∑ y ∈ Y, ∑ f ∈ F y, ((faceVertices f).card : ℝ)⁻¹ := by
  obtain ⟨y0, hy0⟩ := hY
  have hcube : Y.card ≤ 2 ^ n := by
    calc Y.card ≤ (univ : Finset (Qubits n)).card := Finset.card_le_univ Y
      _ = 2 ^ n := by simp
  have hqY : q ≤ Y.card := S200B_clause1 n q Y y0 hy0 (hfaces y0 hy0)
  refine ⟨hqY, hcube, ?_⟩
  intro F hF
  obtain ⟨m, hm⟩ := S200B_charge_eq n q hq (le_trans hqY hcube)
  have hN : (0 : ℝ) < Y.card := by
    have : 0 < Y.card := Finset.card_pos.mpr ⟨y0, hy0⟩
    exact_mod_cast this
  set N : ℝ := (Y.card : ℝ) with hNdef
  set lam : ℝ := (2 : ℝ) ^ m with hlam
  set μ : ℝ := lam / N with hμ
  have hμ0 : 0 ≤ μ := by positivity
  set h : (Fin n → Fin 3) → ℝ := fun f => max (μ * (faceVertices f).card - 1) 0 with hh
  -- step A
  have hA : ∑ y ∈ Y, ∑ f ∈ F y, (μ - ((faceVertices f).card : ℝ)⁻¹ * h f) ≤
      ∑ y ∈ Y, ∑ f ∈ F y, ((faceVertices f).card : ℝ)⁻¹ := by
    apply Finset.sum_le_sum; intro y hy
    apply Finset.sum_le_sum; intro f hf
    apply S200B_term
    have hm' := ((hF y hy).2 f hf).1
    have : 0 < (faceVertices f).card := Finset.card_pos.mpr ⟨y, hm'⟩
    exact_mod_cast this
  have hA2 : ∑ y ∈ Y, ∑ f ∈ F y, (μ - ((faceVertices f).card : ℝ)⁻¹ * h f) =
      q * lam - ∑ y ∈ Y, ∑ f ∈ F y, ((faceVertices f).card : ℝ)⁻¹ * h f := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun y hy => by rw [(hF y hy).1])]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hμ, ← hNdef]
    field_simp
  -- step B
  have hB : ∑ y ∈ Y, ∑ f ∈ F y, ((faceVertices f).card : ℝ)⁻¹ * h f ≤
      ∑ y ∈ Y, ∑ f : Fin n → Fin 3, (if y ∈ faceVertices f ∧ faceVertices f ⊆ Y then
        ((faceVertices f).card : ℝ)⁻¹ * h f else 0) := by
    apply Finset.sum_le_sum; intro y hy
    rw [← Finset.sum_congr rfl (fun f hf => if_pos ((hF y hy).2 f hf))]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro f _ _
    split_ifs
    · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (le_max_right _ _)
    · exact le_rfl
  -- step C
  have hC : ∑ y ∈ Y, ∑ f : Fin n → Fin 3, (if y ∈ faceVertices f ∧ faceVertices f ⊆ Y then
        ((faceVertices f).card : ℝ)⁻¹ * h f else 0) = S200B_L Y μ := by
    rw [Finset.sum_comm]
    unfold S200B_L
    apply Finset.sum_congr rfl; intro f _
    by_cases hs : faceVertices f ⊆ Y
    · simp only [hs, and_true, if_true]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hfil : Y.filter (fun y => y ∈ faceVertices f) = faceVertices f := by
        ext y; constructor
        · intro hy; exact (Finset.mem_filter.mp hy).2
        · intro hy; exact Finset.mem_filter.mpr ⟨hs hy, hy⟩
      rw [hfil]
      by_cases hk : ((faceVertices f).card : ℝ) = 0
      · rw [hk]; simp [hh, hk]
      · rw [← mul_assoc, mul_inv_cancel₀ hk, one_mul]
    · simp [hs]
  have hG := S200B_G n Y μ hμ0
  have hRN : S200B_R n (μ * Y.card) = ∑ x : Qubits n, max (lam - 2 ^ hammingWeight x) 0 := by
    unfold S200B_R
    rw [← hNdef, hμ, div_mul_cancel₀ _ hN.ne']
  rw [hm]
  linarith

end

end QAlgorithms.Papers.Independent.Information100.P62

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

theorem solution (n q : ℕ) (hq : 0 < q) (Y : Finset (Qubits n)) (hY : Y.Nonempty)
    (hfaces : ∀ y ∈ Y, q ≤ (univ.filter (fun F : Fin n → Fin 3 => y ∈ faceVertices F ∧ faceVertices F ⊆ Y)).card) :
    q ≤ Y.card ∧ Y.card ≤ 2 ^ n ∧
    ∀ F : Qubits n → Finset (Fin n → Fin 3),
      (∀ y ∈ Y, (F y).card = q ∧ ∀ f ∈ F y, y ∈ faceVertices f ∧ faceVertices f ⊆ Y) →
      (charge n q : ℝ) ≤ ∑ y ∈ Y, ∑ f ∈ F y, ((faceVertices f).card : ℝ)⁻¹ :=
  S200B_main n q hq Y hY hfaces

end

