-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.deterministic_iff_normalized
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:31:53.269471+00:00
-- url     : https://prove2.me/submissions/477bc90c-2873-46fc-a3aa-9190a61851da

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

lemma dn204_traceLeft_psd {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) (hM : M.PosSemidef) : (traceLeft M).PosSemidef := by
  have : traceLeft M = ∑ a, M.submatrix (fun b => (a, b)) (fun b => (a, b)) := by
    ext b b'; simp [traceLeft, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ fun a _ => hM.submatrix _

lemma dn204_kron_psd_inv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (Q : Matrix β β ℂ) (a0 : α)
    (h : (Matrix.kronecker (1 : Matrix α α ℂ) Q).PosSemidef) : Q.PosSemidef := by
  have e : (Matrix.kronecker (1 : Matrix α α ℂ) Q).submatrix (fun x => (a0, x))
      (fun x => (a0, x)) = Q := by
    ext x y; simp
  rw [← e]; exact h.submatrix _

lemma dn204_tl {α β : Type*} [Fintype α] {_i1 : DecidableEq (α × β)} {_i2 : DecidableEq β}
    (c : ℂ) : traceLeft (c • (1 : Matrix (α × β) (α × β) ℂ)) =
      (c * Fintype.card α) • (1 : Matrix β β ℂ) := by
  ext b b'
  by_cases h : b = b' <;> simp [traceLeft, Matrix.one_apply, h, Finset.sum_const, mul_comm]

lemma dn204_kr {α β : Type*} {_i0 : DecidableEq α} {_i1 : DecidableEq (α × β)}
    {_i2 : DecidableEq β} (c : ℂ) :
    Matrix.kronecker (1 : Matrix α α ℂ) (c • (1 : Matrix β β ℂ)) =
      c • (1 : Matrix (α × β) (α × β) ℂ) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> simp [h1, h2]

lemma dn204_norm_scalar (s : Signature) : ∀ n : ℕ,
    Normalized s n ((((∏ j ∈ Finset.range n, (s.output j : ℝ))⁻¹ : ℝ) : ℂ) •
      (1 : Matrix (Basis s n) (Basis s n) ℂ)) := by
  intro n
  induction n with
  | zero => simp [Normalized]
  | succ n ih =>
    refine ⟨Matrix.PosSemidef.one.smul ?_, _, ih, ?_⟩
    · have : (0:ℝ) ≤ (∏ j ∈ Finset.range (n+1), (s.output j : ℝ))⁻¹ := by positivity
      exact_mod_cast this
    · have hPc : (∏ j ∈ Finset.range n, (s.output j : ℂ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (s.output_pos j).ne'
      have hoc : (s.output n : ℂ) ≠ 0 := by exact_mod_cast (s.output_pos n).ne'
      refine (dn204_tl (α := Fin (s.output n)) (β := Fin (s.input n) × Basis s n)
        (_i2 := Classical.decEq _) _).trans ?_
      refine Eq.trans ?_ (dn204_kr (α := Fin (s.input n)) (β := Basis s n)
        (_i1 := Classical.decEq _) _).symm
      congr 1
      rw [Finset.prod_range_succ, Fintype.card_fin]
      push_cast
      field_simp

lemma dn204_norm_psd (s : Signature) (n : ℕ) (R : Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ)
    (h : Normalized s (n+1) R) : R.PosSemidef := h.1

theorem dn204_norm_iff_aff (s : Signature) : ∀ (n : ℕ) (R : Matrix (Basis s n) (Basis s n) ℂ),
    R.PosSemidef → (Normalized s n R ↔ AffineNormalized s n R)
  | 0, R, _ => Iff.rfl
  | n+1, R, hR => by
    have key : ∀ Q : Matrix (Basis s n) (Basis s n) ℂ,
        traceLeft R = Matrix.kronecker (1 : Matrix (Fin (s.input n)) _ ℂ) Q →
          Q.PosSemidef := by
      intro Q hQ
      have h := dn204_traceLeft_psd R hR
      rw [hQ] at h
      exact dn204_kron_psd_inv Q ⟨0, s.input_pos n⟩ h
    constructor
    · rintro ⟨-, Q, hQ, hT⟩
      exact ⟨Q, (dn204_norm_iff_aff s n Q (key Q hT)).1 hQ, hT⟩
    · rintro ⟨Q, hQ, hT⟩
      exact ⟨hR, Q, (dn204_norm_iff_aff s n Q (key Q hT)).2 hQ, hT⟩

theorem dn204_ins_surj (s : Signature) : ∀ (k : ℕ) (y : Basis s (k+1)),
    ∃ o i x, insertEndpoints s k o i x = y
  | 0, y => ⟨y.1, y.2.1, (), rfl⟩
  | k+1, y => by
    obtain ⟨o', i, x', h⟩ := dn204_ins_surj s k y.2.2
    exact ⟨y.1, i, (y.2.1, o', x'), by simp only [insertEndpoints, h]; rfl⟩

lemma dn204_sum_basis (s : Signature) (k : ℕ) (f : Basis s (k+1) → ℂ) :
    ∑ x, f x = ∑ a : Fin (s.output k), ∑ b : Fin (s.input k), ∑ c : Basis s k, f (a, b, c) := by
  have h1 := Fintype.sum_prod_type (fun x : Fin (s.output k) × (Fin (s.input k) × Basis s k) => f x)
  exact h1.trans (Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _)

lemma dn204_det_psd : ∀ (n : ℕ) (s : Signature) (R : Matrix (Basis s n) (Basis s n) ℂ),
    0 < n → Deterministic n s R → R.PosSemidef
  | 0, _, _, h, _ => absurd h (lt_irrefl 0)
  | 1, _, _, _, h => h.1
  | _+2, _, _, _, h => h.1

open scoped MatrixOrder Matrix.Norms.L2Operator in
lemma dn204_herm_bound {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ)
    (hX : X.IsHermitian) : ∃ B : ℝ, 0 < B ∧ ((B : ℂ) • (1 : Matrix I I ℂ) + X).PosSemidef := by
  have hX' : IsSelfAdjoint (-X) := by
    have : IsSelfAdjoint X := hX
    exact this.neg
  have h := IsSelfAdjoint.le_algebraMap_norm_self (a := -X) hX'
  rw [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] at h
  refine ⟨‖-X‖ + 1, by positivity, ?_⟩
  have e : (((‖-X‖ + 1 : ℝ) : ℂ) • (1 : Matrix I I ℂ) + X) = (‖-X‖ • (1 : Matrix I I ℂ) - -X) + 1 := by
    rw [← Complex.coe_smul]; simp [add_smul]; abel
  rw [e]
  exact h.add Matrix.PosSemidef.one

lemma dn204_slot_psd (s : Signature) (k : ℕ) (R : Matrix (Basis s (k+1)) (Basis s (k+1)) ℂ)
    (T : Matrix (Basis (slots s) k) (Basis (slots s) k) ℂ) (hR : R.PosSemidef)
    (hT : T.PosSemidef) : (slotAction s k R T).PosSemidef := by
  let f : (Fin (s.output k) × Fin (s.input 0)) × Basis (slots s) k → Basis s (k+1) :=
    fun p => insertEndpoints s k p.1.1 p.1.2 p.2
  have hM : ((R.submatrix f f) ⊙ (T.submatrix Prod.snd Prod.snd)).PosSemidef :=
    (hR.submatrix f).hadamard (hT.submatrix _)
  let W : Matrix ((Fin (s.output k) × Fin (s.input 0)) × Basis (slots s) k)
      (Fin (s.output k) × Fin (s.input 0)) ℂ :=
    Matrix.of fun p a => if p.1 = a then (1 : ℂ) else 0
  have e : slotAction s k R T =
      Wᴴ * ((R.submatrix f f) ⊙ (T.submatrix Prod.snd Prod.snd)) * W := by
    ext a b
    simp [slotAction, W, Matrix.mul_apply, Fintype.sum_prod_type, f, Matrix.conjTranspose_apply]
    exact Finset.sum_comm
  rw [e]; exact hM.conjTranspose_mul_mul_same W

instance dn204_uniq (s : Signature) : Unique (Basis s 0) := inferInstanceAs (Unique Unit)

lemma dn204_slot0 (s : Signature) (Q : Matrix (Basis s 1) (Basis s 1) ℂ) :
    slotAction s 0 Q 1 = Q.submatrix (fun a => (a.1, a.2, ())) (fun a => (a.1, a.2, ())) := by
  ext a b
  simp only [slotAction, Fintype.sum_unique, Matrix.one_apply_eq, mul_one, insertEndpoints]
  rfl

lemma dn204_tl_apply {α β : Type*} [Fintype α] (M : Matrix (α × β) (α × β) ℂ) (b b' : β) :
    traceLeft M b b' = ∑ a, M (a, b) (a, b') := rfl

lemma dn204_pull {A B C D E : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype E] (f : A → B → C → D → E → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e = ∑ b, ∑ c, ∑ e, ∑ d, ∑ a, f a b c d e := by
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_
  calc ∑ a, ∑ d, ∑ e, f a b c d e = ∑ d, ∑ a, ∑ e, f a b c d e := Finset.sum_comm
  _ = ∑ d, ∑ e, ∑ a, f a b c d e := Finset.sum_congr rfl fun d _ => Finset.sum_comm
  _ = _ := Finset.sum_comm

theorem dn204_trace_identity (s : Signature) (k : ℕ)
    (R : Matrix (Basis s (k+2)) (Basis s (k+2)) ℂ)
    (Q : Matrix (Basis s (k+1)) (Basis s (k+1)) ℂ)
    (hR : traceLeft R = Matrix.kronecker (1 : Matrix (Fin (s.input (k+1))) _ ℂ) Q)
    (T : Matrix (Basis (slots s) (k+1)) (Basis (slots s) (k+1)) ℂ)
    (T'' : Matrix (Basis (slots s) k) (Basis (slots s) k) ℂ)
    (hT : traceLeft T = Matrix.kronecker (1 : Matrix (Fin ((slots s).input k)) _ ℂ) T'') :
    traceLeft (slotAction s (k+1) R T) = traceLeft (slotAction s k Q T'') := by
  have hR' : ∀ (a b : Fin ((slots s).output k)) x y, ∑ o : Fin (s.output (k+1)), R (o, a, x) (o, b, y) =
      (if a = b then 1 else 0) * Q x y := by
    intro a b x y
    have := congrFun (congrFun hR (a, x)) (b, y)
    simp only [traceLeft, Matrix.of_apply] at this
    rw [this]; clear this
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
    try (split_ifs <;> (try simp_all) <;> exact absurd rfl ‹_›)
  have hT' : ∀ (a b : Fin ((slots s).input k)) x y, ∑ c : Fin ((slots s).output k), T (c, a, x) (c, b, y) =
      (if a = b then 1 else 0) * T'' x y := by
    intro a b x y
    have := congrFun (congrFun hT (a, x)) (b, y)
    simp only [traceLeft, Matrix.of_apply] at this
    rw [this]; clear this
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
  ext i i'
  simp only [dn204_tl_apply, slotAction, insertEndpoints]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans ?_
  simp only [← Finset.sum_mul, hR']
  simp only [dn204_sum_basis (slots s) k]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [dn204_pull]
  simp only [← Finset.mul_sum, hT', mul_ite, ite_mul, one_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

lemma dn204_tl_add {α β : Type*} [Fintype α] (M N : Matrix (α × β) (α × β) ℂ) :
    traceLeft (M + N) = traceLeft M + traceLeft N := by
  ext b b'; simp [dn204_tl_apply, Finset.sum_add_distrib]

lemma dn204_tl_smul {α β : Type*} [Fintype α] (c : ℂ) (M : Matrix (α × β) (α × β) ℂ) :
    traceLeft (c • M) = c • traceLeft M := by
  ext b b'; simp [dn204_tl_apply, Finset.mul_sum]

lemma dn204_tl_ct {α β : Type*} [Fintype α] (M : Matrix (α × β) (α × β) ℂ) :
    traceLeft Mᴴ = (traceLeft M)ᴴ := by
  ext b b'; simp [dn204_tl_apply, Matrix.conjTranspose_apply]

lemma dn204_tl_kron {α β : Type*} [Fintype α] (C : Matrix α α ℂ) (D : Matrix β β ℂ) :
    traceLeft (Matrix.kronecker C D) = C.trace • D := by
  ext b b'
  simp [traceLeft, Matrix.kronecker, Matrix.trace, Finset.sum_mul]

lemma dn204_btl_add (s : Signature) (k : ℕ) (M N : Matrix (Basis s (k+1)) (Basis s (k+1)) ℂ) :
    traceLeft (M + N) = traceLeft M + traceLeft N := dn204_tl_add M N

lemma dn204_btl_smul (s : Signature) (k : ℕ) (c : ℂ)
    (M : Matrix (Basis s (k+1)) (Basis s (k+1)) ℂ) :
    traceLeft (c • M) = c • traceLeft M := dn204_tl_smul c M

lemma dn204_btl_ct (s : Signature) (k : ℕ) (M : Matrix (Basis s (k+1)) (Basis s (k+1)) ℂ) :
    traceLeft Mᴴ = (traceLeft M)ᴴ := dn204_tl_ct M

theorem dn204_link_channel (s : Signature) : ∀ (k : ℕ)
    (Q : Matrix (Basis s (k+1)) (Basis s (k+1)) ℂ)
    (T : Matrix (Basis (slots s) k) (Basis (slots s) k) ℂ),
    Normalized s (k+1) Q → Normalized (slots s) k T → ChannelChoi (slotAction s k Q T)
  | 0, Q, T, hQ, hT => by
    have hT1 : T = 1 := hT
    subst hT1
    obtain ⟨hQp, Q0, hQ0, htl⟩ := hQ
    have hQ01 : Q0 = 1 := hQ0
    subst hQ01
    refine ⟨?_, ?_⟩
    · rw [dn204_slot0]; exact hQp.submatrix _
    · rw [dn204_slot0]
      ext i i'
      have := congrFun (congrFun htl (i, ())) (i', ())
      refine (Eq.trans (rfl : _ = traceLeft Q (i, ()) (i', ())) this).trans ?_
      simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one]
      first | rfl | (by_cases h : i = i' <;> simp [Matrix.one_apply, h])
  | k+1, Q, T, hQ, hT => by
    obtain ⟨hQp, Q', hQ', htlQ⟩ := hQ
    obtain ⟨hTp, T'', hT'', htlT⟩ := hT
    refine ⟨dn204_slot_psd s (k+1) Q T hQp hTp, ?_⟩
    rw [dn204_trace_identity s k Q Q' htlQ T T'' htlT]
    exact (dn204_link_channel s k Q' T'' hQ' hT'').2

lemma dn204_G_apply (s : Signature) (n : ℕ) (R : Matrix (Basis s (n+2)) (Basis s (n+2)) ℂ)
    (X : Matrix (Basis (slots s) (n+1)) (Basis (slots s) (n+1)) ℂ) (i i' : Fin (s.input 0)) :
    traceLeft (slotAction s (n+1) R X) i i' = ∑ u, ∑ v,
      traceLeft R (u.1, insertEndpoints s n u.2.1 i u.2.2)
        (v.1, insertEndpoints s n v.2.1 i' v.2.2) * X u v := by
  simp only [dn204_tl_apply, slotAction, insertEndpoints]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_mul]; rfl

lemma dn204_G_add (s : Signature) (k : ℕ) (R : Matrix (Basis s (k+1)) (Basis s (k+1)) ℂ)
    (X Y : Matrix (Basis (slots s) k) (Basis (slots s) k) ℂ) :
    traceLeft (slotAction s k R (X + Y)) =
      traceLeft (slotAction s k R X) + traceLeft (slotAction s k R Y) := by
  ext i i'; simp [dn204_tl_apply, slotAction, mul_add, Finset.sum_add_distrib]

lemma dn204_G_sub (s : Signature) (k : ℕ) (R : Matrix (Basis s (k+1)) (Basis s (k+1)) ℂ)
    (X Y : Matrix (Basis (slots s) k) (Basis (slots s) k) ℂ) :
    traceLeft (slotAction s k R (X - Y)) =
      traceLeft (slotAction s k R X) - traceLeft (slotAction s k R Y) := by
  ext i i'; simp [dn204_tl_apply, slotAction, mul_sub, Finset.sum_sub_distrib]

lemma dn204_G_smul (s : Signature) (k : ℕ) (R : Matrix (Basis s (k+1)) (Basis s (k+1)) ℂ)
    (c : ℂ) (X : Matrix (Basis (slots s) k) (Basis (slots s) k) ℂ) :
    traceLeft (slotAction s k R (c • X)) = c • traceLeft (slotAction s k R X) := by
  ext i i'; simp [dn204_tl_apply, slotAction, Finset.mul_sum, mul_left_comm]

lemma dn204_tl_parts {α β : Type*} [Fintype α] (X : Matrix (α × β) (α × β) ℂ)
    (hX : traceLeft X = 0) :
    traceLeft ((1/2 : ℂ) • (X + Xᴴ)) = 0 ∧ traceLeft ((-Complex.I/2) • (X - Xᴴ)) = 0 := by
  have hXt : traceLeft Xᴴ = 0 := by rw [dn204_tl_ct, hX, Matrix.conjTranspose_zero]
  constructor
  · rw [dn204_tl_smul, dn204_tl_add, hX, hXt]; simp
  · rw [dn204_tl_smul, sub_eq_add_neg, dn204_tl_add, ← neg_one_smul ℂ Xᴴ,
      dn204_tl_smul, hX, hXt]; simp

theorem dn204_G_zero (s : Signature) (n : ℕ) (R : Matrix (Basis s (n+2)) (Basis s (n+2)) ℂ)
    (H : ∀ T, Normalized (slots s) (n+1) T → ChannelChoi (slotAction s (n+1) R T))
    (X : Matrix (Basis (slots s) (n+1)) (Basis (slots s) (n+1)) ℂ) (hX : traceLeft X = 0) :
    traceLeft (slotAction s (n+1) R X) = 0 := by
  have herm : ∀ Y : Matrix (Basis (slots s) (n+1)) (Basis (slots s) (n+1)) ℂ,
      Y.IsHermitian → traceLeft Y = 0 → traceLeft (slotAction s (n+1) R Y) = 0 := by
    intro Y hY hYt
    have hT0 := dn204_norm_scalar (slots s) (n+1)
    set c : ℝ := (∏ j ∈ Finset.range (n+1), ((slots s).output j : ℝ))⁻¹ with hc
    have hcpos : 0 < c :=
      inv_pos.mpr (Finset.prod_pos fun j _ => by exact_mod_cast (slots s).output_pos j)
    obtain ⟨B, hB, hBY⟩ := dn204_herm_bound Y hY
    obtain ⟨T0, hT0def⟩ : ∃ T0 : Matrix (Basis (slots s) (n+1)) (Basis (slots s) (n+1)) ℂ,
        T0 = (c : ℂ) • (1 : Matrix (Basis (slots s) (n+1)) _ ℂ) := ⟨_, rfl⟩
    rw [← hT0def] at hT0
    have hT1 : Normalized (slots s) (n+1) (T0 + ((c / B : ℝ) : ℂ) • Y) := by
      obtain ⟨-, Q0, hQ0, htl0⟩ := hT0
      refine ⟨?_, Q0, hQ0, ?_⟩
      · have e : T0 + ((c/B : ℝ) : ℂ) • Y = ((c/B : ℝ) : ℂ) • ((B : ℂ) • 1 + Y) := by
          rw [hT0def, smul_add, smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ hB.ne']
        rw [e]; exact hBY.smul (by exact_mod_cast (div_pos hcpos hB).le)
      · rw [dn204_btl_add, dn204_btl_smul, hYt, smul_zero, add_zero]; exact htl0
    have h1 := (H _ hT1).2
    have h0 := (H _ hT0).2
    rw [dn204_G_add, dn204_G_smul, h0] at h1
    have h2 : ((c/B : ℝ) : ℂ) • traceLeft (slotAction s (n+1) R Y) = 0 := by
      simpa using h1
    rcases smul_eq_zero.mp h2 with h | h
    · exfalso
      have : (c / B : ℝ) ≠ 0 := (div_pos hcpos hB).ne'
      exact this (by exact_mod_cast h)
    · exact h
  obtain ⟨Y1, hY1⟩ : ∃ Y : Matrix (Basis (slots s) (n+1)) (Basis (slots s) (n+1)) ℂ,
      Y = (1/2 : ℂ) • (X + Xᴴ) := ⟨_, rfl⟩
  obtain ⟨Y2, hY2⟩ : ∃ Y : Matrix (Basis (slots s) (n+1)) (Basis (slots s) (n+1)) ℂ,
      Y = (-Complex.I/2) • (X - Xᴴ) := ⟨_, rfl⟩
  have hXe : X = Y1 + Complex.I • Y2 := by
    ext a b
    simp only [hY1, hY2, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]; ring
  have h1 : Y1.IsHermitian := by
    subst hY1
    ext a b
    simp [Matrix.conjTranspose_apply, add_comm]
    ring
  have h2 : Y2.IsHermitian := by
    subst hY2
    ext a b
    simp [Matrix.conjTranspose_apply]
    ring
  have t1 : traceLeft Y1 = 0 := by rw [hY1]; exact (dn204_tl_parts X hX).1
  have t2 : traceLeft Y2 = 0 := by rw [hY2]; exact (dn204_tl_parts X hX).2
  rw [hXe, dn204_G_add, dn204_G_smul, herm Y1 h1 t1, herm Y2 h2 t2]; simp

lemma dn204_kron_one_congr {A U : Type*} (C : Matrix A A ℂ) {d1 d2 : DecidableEq U} :
    Matrix.kronecker C (@OfNat.ofNat (Matrix U U ℂ) 1 (@One.toOfNat1 _ (@Matrix.one U ℂ d1 _ _))) =
      Matrix.kronecker C
        (@OfNat.ofNat (Matrix U U ℂ) 1 (@One.toOfNat1 _ (@Matrix.one U ℂ d2 _ _))) := by
  obtain rfl : d1 = d2 := Subsingleton.elim _ _
  rfl

lemma dn204_tl_unit {O A U : Type*} [Fintype O] [Unique U] {dA dA' : DecidableEq A}
    {dU : DecidableEq U} (Q : Matrix (O × (A × U)) (O × (A × U)) ℂ)
    (h : traceLeft (Q.submatrix (fun a : O × A => (a.1, a.2, (default : U)))
      (fun a : O × A => (a.1, a.2, (default : U)))) =
        (@OfNat.ofNat (Matrix A A ℂ) 1 (@One.toOfNat1 _ (@Matrix.one A ℂ dA _ _)))) :
    traceLeft Q = Matrix.kronecker
      (@OfNat.ofNat (Matrix A A ℂ) 1 (@One.toOfNat1 _ (@Matrix.one A ℂ dA' _ _)))
      (@OfNat.ofNat (Matrix U U ℂ) 1 (@One.toOfNat1 _ (@Matrix.one U ℂ dU _ _))) := by
  obtain rfl : dA = dA' := Subsingleton.elim _ _
  ext p q
  obtain ⟨i, u⟩ := p
  obtain ⟨i', u'⟩ := q
  obtain rfl : u = default := Subsingleton.elim _ _
  obtain rfl : u' = default := Subsingleton.elim _ _
  have := congrFun (congrFun h i) i'
  simp only [traceLeft, Matrix.of_apply, Matrix.submatrix_apply] at this
  simp only [traceLeft, Matrix.of_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply_eq, mul_one]
  exact this

lemma dn204_factor_gen {A W Y I : Type*} [Fintype A] [Fintype W] [DecidableEq A]
    (P : Matrix (A × Y) (A × Y) ℂ) (ins : W → I → Y) (hsurj : ∀ y, ∃ w i, ins w i = y)
    (a0 : A)
    (hG : ∀ X : Matrix (A × W) (A × W) ℂ, traceLeft X = 0 → ∀ i i',
      ∑ u, ∑ v, P (u.1, ins u.2 i) (v.1, ins v.2 i') * X u v = 0) :
    P = Matrix.kronecker (1 : Matrix A A ℂ) (P.submatrix (fun y => (a0, y)) (fun y => (a0, y))) := by
  classical
  let E : A × W → A × W → Matrix (A × W) (A × W) ℂ :=
    fun u0 v0 => Matrix.of fun u v => if u = u0 ∧ v = v0 then 1 else 0
  have hE : ∀ u0 v0 i i', ∑ u, ∑ v, P (u.1, ins u.2 i) (v.1, ins v.2 i') * E u0 v0 u v =
      P (u0.1, ins u0.2 i) (v0.1, ins v0.2 i') := by
    intro u0 v0 i i'
    simp [E, ite_and]
  have off : ∀ (a b : A) (w w' : W) i i', a ≠ b →
      P (a, ins w i) (b, ins w' i') = 0 := by
    intro a b w w' i i' hab
    have h0 : traceLeft (E (a, w) (b, w')) = 0 := by
      ext x y
      simp only [traceLeft, E, Matrix.of_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hab ((congrArg Prod.fst h1).symm.trans (congrArg Prod.fst h2))
    have := hG _ h0 i i'
    rw [hE] at this; exact this
  have diag : ∀ (a b : A) (w w' : W) i i',
      P (a, ins w i) (a, ins w' i') = P (b, ins w i) (b, ins w' i') := by
    intro a b w w' i i'
    have h0 : traceLeft (E (a, w) (a, w') - E (b, w) (b, w')) = 0 := by
      ext x y
      simp only [traceLeft, E, Matrix.of_apply, Matrix.zero_apply, Matrix.sub_apply,
        Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      by_cases hx : x = w <;> by_cases hy : y = w' <;> simp [Prod.ext_iff, hx, hy]
    have := hG _ h0 i i'
    simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, hE, sub_eq_zero] at this
    exact this
  ext p q
  obtain ⟨a, y⟩ := p
  obtain ⟨b, y'⟩ := q
  obtain ⟨w, i, rfl⟩ := hsurj y
  obtain ⟨w', i', rfl⟩ := hsurj y'
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.submatrix_apply]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq, one_mul]
    exact diag a a0 w w' i i'
  · rw [Matrix.one_apply_ne hab, zero_mul]
    exact off a b w w' i i' hab

theorem dn204_factor (s : Signature) (n : ℕ) (R : Matrix (Basis s (n+2)) (Basis s (n+2)) ℂ)
    (hR : R.PosSemidef)
    (H : ∀ T, Normalized (slots s) (n+1) T → ChannelChoi (slotAction s (n+1) R T)) :
    ∃ Q : Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ, Q.PosSemidef ∧
      traceLeft R = Matrix.kronecker (1 : Matrix (Fin (s.input (n+1))) _ ℂ) Q := by
  have hG := dn204_G_zero s n R H
  refine ⟨(traceLeft R).submatrix (fun y => ((⟨0, s.input_pos _⟩ : Fin (s.input (n+1))), y))
    (fun y => ((⟨0, s.input_pos _⟩ : Fin (s.input (n+1))), y)),
    (dn204_traceLeft_psd R hR).submatrix _, ?_⟩
  refine dn204_factor_gen (W := Fin (s.output n) × Basis (slots s) n) (I := Fin (s.input 0))
    (traceLeft R) (fun w i => insertEndpoints s n w.1 i w.2) ?_ _ ?_
  · intro y
    obtain ⟨o, i, x, h⟩ := dn204_ins_surj s n y
    exact ⟨(o, x), i, h⟩
  · intro X hX i i'
    exact (dn204_G_apply s n R X i i').symm.trans (congrFun (congrFun (hG X hX) i) i')

theorem dn204_main : ∀ (n : ℕ) (s : Signature) (S : Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ),
    S.PosSemidef → (Deterministic (n+1) s S ↔ Normalized s (n+1) S) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro s S hS
  match n, IH with
  | 0, _ =>
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, 1, rfl, h2.trans (dn204_kron_one_congr _)⟩
    · rintro ⟨h1, Q, hQ, h2⟩
      have : Q = 1 := hQ
      subst this
      exact ⟨h1, h2.trans (dn204_kron_one_congr _)⟩
  | m+1, IH =>
    constructor
    · rintro ⟨-, H⟩
      have Hn : ∀ T, Normalized (slots s) (m+1) T →
          ChannelChoi (slotAction s (m+1) S T) := by
        intro T hT
        exact H T ((IH m (by omega) (slots s) T hT.1).2 hT)
      obtain ⟨Q, hQ, htl⟩ := dn204_factor s m S hS Hn
      have hQdet : Deterministic (m+1) s Q := by
        rcases m with _ | m'
        ·
          refine ⟨hQ, ?_⟩
          have hT := dn204_norm_scalar (slots s) 1
          obtain ⟨_, Q'', hQ'', htlT⟩ := id hT
          have hQ''1 : Q'' = 1 := hQ''
          have h := (Hn _ hT).2
          rw [dn204_trace_identity s 0 S Q htl _ Q'' htlT, hQ''1, dn204_slot0] at h
          exact dn204_tl_unit Q h
        ·
          refine ⟨hQ, fun T' hT' => ?_⟩
          have hT'p := dn204_det_psd _ _ _ (by omega) hT'
          have hT'N := (IH m' (by omega) (slots s) T' hT'p).1 hT'
          have hd : (s.input (m'+2) : ℂ) ≠ 0 := by exact_mod_cast (s.input_pos _).ne'
          let T : Matrix (Basis (slots s) (m'+2)) (Basis (slots s) (m'+2)) ℂ :=
            ((s.input (m'+2) : ℂ)⁻¹) • Matrix.kronecker (1 : Matrix (Fin (s.input (m'+2))) (Fin (s.input (m'+2))) ℂ)
              (Matrix.kronecker (1 : Matrix (Fin (s.output (m'+1))) (Fin (s.output (m'+1))) ℂ) T')
          have htlT : traceLeft T =
              Matrix.kronecker (1 : Matrix (Fin ((slots s).input (m'+1))) _ ℂ) T' := by
            show traceLeft (((s.input (m'+2) : ℂ)⁻¹) • Matrix.kronecker
              (1 : Matrix (Fin (s.input (m'+2))) (Fin (s.input (m'+2))) ℂ)
              (Matrix.kronecker (1 : Matrix (Fin (s.output (m'+1))) (Fin (s.output (m'+1))) ℂ)
                T')) = _
            rw [dn204_tl_smul, dn204_tl_kron, Matrix.trace_one, Fintype.card_fin, smul_smul,
              inv_mul_cancel₀ (by exact_mod_cast (s.input_pos _).ne'), one_smul]
            rfl
          have hTp : T.PosSemidef := by
            refine Matrix.PosSemidef.smul ?_ ?_
            · exact Matrix.PosSemidef.one.kronecker (Matrix.PosSemidef.one.kronecker hT'p)
            · exact inv_nonneg.mpr (by exact_mod_cast (Nat.zero_le _))
          have h := (Hn T ⟨hTp, T', hT'N, htlT⟩).2
          rw [dn204_trace_identity s (m'+1) S Q htl T T' htlT] at h
          exact ⟨dn204_slot_psd s (m'+1) Q T' hQ hT'p, h⟩
      exact ⟨hS, Q, (IH m (by omega) s Q hQ).1 hQdet, htl⟩
    · intro hN
      refine ⟨hS, fun T hT => ?_⟩
      exact dn204_link_channel s (m+1) S T hN
        ((IH m (by omega) (slots s) T (dn204_det_psd _ _ _ (by omega) hT)).1 hT)

end QAlgorithms.Papers.Independent.Dependency50.P26

open QAlgorithms.Papers.Independent.Dependency50.P26 in
/-- PDF pp.11–12, Theorem 5: independent operational and trace-recursive presentations. -/
theorem solution (s : Signature) (n : ℕ) (hn : 0 < n)
    (S : Matrix (Basis s n) (Basis s n) ℂ) (hS : S.PosSemidef) :
    Deterministic n s S ↔ Normalized s n S := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact dn204_main m s S hS


end
