-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P34.catalytic_coherent_bit_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T03:57:46.307585+00:00
-- url     : https://prove2.me/submissions/be2c587c-61ee-46dc-b8f9-57afe4e2fdd4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34
noncomputable section
open scoped Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P34
instance g65g_uq : Unique (Qubits 0) := Pi.uniqueOfIsEmpty _

lemma g65g_kr {K ι κ : Type} [Fintype K] [Fintype ι] (E : K → Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) (i j : κ) :
    krausApply E ρ i j = ∑ k, ∑ a, ∑ b, E k i a * ρ a b * conj (E k j b) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]; rfl

lemma g65g_s1 (f : Qubits 1 → ℂ) : ∑ b, f b = f (fun _ => false) + f (fun _ => true) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool, add_comm]; rfl

lemma g65g_s2 (f : Qubits 2 → ℂ) : ∑ b, f b = f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
  simp [finTwoArrowEquiv]; ring

def g65g_pz (x : Qubits 2) (q a : Bool) : ℂ := if q = xor a (x 0) then (if (x 1 && a) then -1 else 1) else 0

def g65g_g (k : Fin 4) : Qubits 2 := ![decide (k.val % 2 = 1), decide (k.val / 2 = 1)]

def g65g_c : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma g65g_feq (a b : Bool) : ((fun _ : Fin 1 => a) = (fun _ => b)) = (a = b) := by
  apply propext; constructor
  · intro h; exact congrFun h 0
  · intro h; rw [h]

lemma g65g_c2 : g65g_c * g65g_c = 1 / 2 := by
  unfold g65g_c
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma g65g_veq (a b c d : Bool) : (![a, b] = ![c, d]) = (a = c ∧ b = d) := by
  apply propext; constructor
  · intro h; exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma g65g_pzc (x : Qubits 2) (q a : Bool) : (starRingEnd ℂ) (g65g_pz x q a) = g65g_pz x q a := by
  unfold g65g_pz; split_ifs <;> simp

lemma g65g_cc : (starRingEnd ℂ) g65g_c = g65g_c := by
  unfold g65g_c; rw [map_inv₀, Complex.conj_ofReal]

lemma g65g_x2 (x : Qubits 2) : x = ![x 0, x 1] := by funext t; fin_cases t <;> rfl
lemma g65g_x1 (x : Qubits 1) : x = fun _ => x 0 := by funext t; fin_cases t; rfl


def g65g_idx (x : Qubits 2) : Fin 4 := ⟨(x 0).toNat + 2 * (x 1).toNat, by
  cases x 0 <;> cases x 1 <;> simp⟩

def g65g_g8 (m : Fin 8) : Qubits 2 × Qubits 1 :=
  (![decide (m.val % 2 = 1), decide (m.val / 2 % 2 = 1)], fun _ => decide (m.val / 4 = 1))

def g65g_idx8 (p : Qubits 2 × Qubits 1) : Fin 8 := ⟨(p.1 0).toNat + 2 * (p.1 1).toNat + 4 * (p.2 0).toNat, by
  cases p.1 0 <;> cases p.1 1 <;> cases p.2 0 <;> simp⟩

lemma g65g_g8idx (x : Qubits 2) (b : Qubits 1) : g65g_g8 (g65g_idx8 (x, b)) = (x, b) := by
  rw [g65g_x2 x, g65g_x1 b]; generalize x 0 = a, x 1 = c, b 0 = d
  cases a <;> cases c <;> cases d <;> rfl

lemma g65g_beta (x y : Qubits 2) :
    ∑ e : Qubits 1, ∑ q : Qubits 1, g65g_pz y (q 0) (e 0) * g65g_pz x (q 0) (e 0) =
      if x = y then 2 else 0 := by
  rw [g65g_x2 x, g65g_x2 y]
  generalize x 0 = a, x 1 = b, y 0 = c, y 1 = d
  simp only [g65g_s1, g65g_veq]
  cases a <;> cases b <;> cases c <;> cases d <;> simp [g65g_pz] <;> norm_num

lemma g65g_v2 (a b c d : Bool) : (![a, b] = ![c, d]) = (a = c ∧ b = d) := g65g_veq a b c d

def g65g_enc : Superop (Qubits 2 × (Unit × Qubits 2)) (Unit × (Fin 8 × (Qubits 1 × Qubits 0))) :=
  fun ρ => Matrix.of fun o o' => ∑ a : Qubits 1, ∑ a' : Qubits 1,
    g65g_pz (g65g_g8 o.2.1).1 (o.2.2.1 0) (a 0) *
      ρ ((g65g_g8 o.2.1).1, ((), ![a 0, (g65g_g8 o.2.1).2 0]))
        ((g65g_g8 o'.2.1).1, ((), ![a' 0, (g65g_g8 o'.2.1).2 0])) *
      g65g_pz (g65g_g8 o'.2.1).1 (o'.2.2.1 0) (a' 0)

def g65g_ali : Superop (Unit × Fin 8) (Qubits 2 × Qubits 1) :=
  fun ρ => Matrix.of fun o o' => ρ ((), g65g_idx8 o) ((), g65g_idx8 o')

def g65g_bob : Superop (Unit × (Unit × (Qubits 2 × (Qubits 1 × Qubits 0)))) (Qubits 2 × Qubits 1) :=
  fun ρ => Matrix.of fun o o' => ∑ e : Qubits 1, ∑ q : Qubits 1, ∑ e' : Qubits 1, ∑ q' : Qubits 1,
    g65g_pz o.1 (q 0) (e 0) * g65g_c * ρ ((), ((), (![e 0, o.2 0], (q, default)))) ((), ((), (![e' 0, o'.2 0], (q', default)))) *
      (g65g_pz o'.1 (q' 0) (e' 0) * g65g_c)

lemma g65g_s2' (f : Qubits 2 → ℂ) : ∑ a, f a = ∑ e : Qubits 1, ∑ b : Bool, f ![e 0, b] := by
  rw [g65g_s2, g65g_s1]
  simp only [Fintype.sum_bool]
  ring

lemma g65g_s2c (c : Bool) (f : Qubits 2 → ℂ) :
    ∑ e : Qubits 2, (if e 1 = c then f e else 0) = ∑ e0 : Qubits 1, f ![e0 0, c] := by
  rw [g65g_s2, g65g_s1]
  cases c <;> simp

lemma g65g_sie (c : Bool) (f : Bool → ℂ) : ∑ b : Bool, (if b = c then f b else 0) = f c := by
  cases c <;> simp [Fintype.sum_bool]

def g65g_V : Fin 1 → Matrix (Unit × (Fin 8 × (Qubits 1 × Qubits 0))) (Qubits 2 × (Unit × Qubits 2)) ℂ :=
  fun _ o i => if i.1 = (g65g_g8 o.2.1).1 ∧ i.2.2 1 = (g65g_g8 o.2.1).2 0 then
    g65g_pz (g65g_g8 o.2.1).1 (o.2.2.1 0) (i.2.2 0) else 0

def g65g_A : Fin 1 → Matrix (Qubits 2 × Qubits 1) (Unit × Fin 8) ℂ :=
  fun _ o i => if i.2 = g65g_idx8 o then 1 else 0

def g65g_B : Fin 1 → Matrix (Qubits 2 × Qubits 1) (Unit × (Unit × (Qubits 2 × (Qubits 1 × Qubits 0)))) ℂ :=
  fun _ o i => if i.2.2.1 1 = o.2 0 then g65g_pz o.1 (i.2.2.2.1 0) (i.2.2.1 0) * g65g_c else 0

lemma g65g_A_kraus : IsKrausFamily g65g_A := by
  unfold IsKrausFamily
  ext ⟨u, m⟩ ⟨u', m'⟩
  obtain rfl : u = u' := Subsingleton.elim _ _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_unique, Fintype.sum_prod_type, g65g_s2, g65g_s1, Matrix.one_apply]
  fin_cases m <;> fin_cases m' <;> simp [g65g_A, g65g_idx8] <;> decide

lemma g65g_ali_eq (ρ : Matrix (Unit × Fin 8) (Unit × Fin 8) ℂ) : g65g_ali ρ = krausApply g65g_A ρ := by
  ext o o'
  rw [g65g_kr]
  simp [g65g_ali, g65g_A, Fintype.sum_prod_type, Finset.sum_ite_eq']

lemma g65g_B_kraus : IsKrausFamily g65g_B := by
  unfold IsKrausFamily
  ext ⟨u, w, e, q, c⟩ ⟨u', w', e', q', c'⟩
  rw [g65g_x2 e, g65g_x2 e', g65g_x1 q, g65g_x1 q']
  generalize e 0 = a0, e 1 = a1, e' 0 = b0, e' 1 = b1, q 0 = c0, q' 0 = d0
  obtain rfl : c = c' := Subsingleton.elim _ _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_unique, g65g_s2, g65g_s1, Fin.sum_univ_one, Matrix.one_apply]
  have hc2 := g65g_c2
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases c0 <;> cases d0 <;>
    simp [g65g_B, g65g_pz, g65g_feq, g65g_cc, g65g_veq] <;>
    (ring_nf; try rw [show g65g_c ^ 2 = 1 / 2 by rw [sq, g65g_c2]]; try norm_num)

lemma g65g_bob_eq (ρ : Matrix (Unit × (Unit × (Qubits 2 × (Qubits 1 × Qubits 0)))) (Unit × (Unit × (Qubits 2 × (Qubits 1 × Qubits 0)))) ℂ) :
    g65g_bob ρ = krausApply g65g_B ρ := by
  ext o o'
  rw [g65g_kr]
  simp only [g65g_bob, g65g_B, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_one,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
    apply_ite (starRingEnd ℂ), map_zero, map_mul, g65g_pzc, g65g_cc, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, g65g_s2c]
  have k1 : ∀ (y : Qubits 2) (b : Qubits 1),
      (((), (), y, b, (@default (Qubits 0) Pi.instInhabited)) :
        Unit × (Unit × (Qubits 2 × (Qubits 1 × Qubits 0)))) =
      ((@default Unit _), (@default Unit _), y, b, (@default (Qubits 0) Unique.instInhabited)) :=
    fun y b => Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _))))
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [k1, k1]

lemma g65g_enc_eq (ρ : Matrix (Qubits 2 × (Unit × Qubits 2)) (Qubits 2 × (Unit × Qubits 2)) ℂ) :
    g65g_enc ρ = krausApply g65g_V ρ := by
  ext o o'
  rw [g65g_kr]
  simp only [g65g_enc, g65g_V, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_one,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
    apply_ite (starRingEnd ℂ), map_zero, g65g_pzc, ite_and, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, g65g_s2c]

lemma g65g_idx8g (m : Fin 8) : g65g_idx8 (g65g_g8 m) = m := by
  fin_cases m <;> rfl

lemma g65g_idx8_inj (p p' : Qubits 2 × Qubits 1) : g65g_idx8 p = g65g_idx8 p' ↔ p = p' := by
  constructor
  · intro h
    have := congrArg g65g_g8 h
    obtain ⟨x, b⟩ := p; obtain ⟨x', b'⟩ := p'
    rwa [g65g_g8idx, g65g_g8idx] at this
  · intro h; rw [h]

lemma g65g_perm2 (x : Qubits 2) (c d : Bool) :
    ∑ q : Qubits 1, g65g_pz x (q 0) c * g65g_pz x (q 0) d = if c = d then 1 else 0 := by
  rw [g65g_x2 x]; generalize x 0 = a, x 1 = b
  simp only [g65g_s1]
  cases a <;> cases b <;> cases c <;> cases d <;> simp [g65g_pz]

lemma g65g_Vform (k : Fin 1) (o : Unit × (Fin 8 × (Qubits 1 × Qubits 0))) (i : Qubits 2 × (Unit × Qubits 2)) :
    g65g_V k o i = if o.2.1 = g65g_idx8 (i.1, fun _ => i.2.2 1) then
      g65g_pz i.1 (o.2.2.1 0) (i.2.2 0) else 0 := by
  unfold g65g_V
  have key : (i.1 = (g65g_g8 o.2.1).1 ∧ i.2.2 1 = (g65g_g8 o.2.1).2 0) ↔
      o.2.1 = g65g_idx8 (i.1, fun _ => i.2.2 1) := by
    constructor
    · rintro ⟨h1, h2⟩
      rw [← g65g_idx8g o.2.1]
      congr 1
      refine Prod.ext h1.symm (funext fun t => ?_)
      fin_cases t; exact h2.symm
    · intro h; rw [h, g65g_g8idx]; exact ⟨rfl, rfl⟩
  by_cases h : o.2.1 = g65g_idx8 (i.1, fun _ => i.2.2 1)
  · rw [if_pos (key.2 h), if_pos h, ← (key.2 h).1]
  · rw [if_neg (mt key.1 h), if_neg h]

lemma g65g_V_kraus : IsKrausFamily g65g_V := by
  unfold IsKrausFamily
  ext ⟨x, u, a⟩ ⟨x', u', a'⟩
  obtain rfl : u = u' := Subsingleton.elim _ _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, g65g_Vform, Fintype.sum_prod_type,
    Fintype.sum_unique, apply_ite (starRingEnd ℂ), map_zero, g65g_pzc, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Matrix.one_apply]
  by_cases hq : g65g_idx8 (x', fun _ => a' 1) = g65g_idx8 (x, fun _ => a 1)
  · have hp := (g65g_idx8_inj _ _).1 hq
    simp only [hq, if_true]
    obtain ⟨h1, h2⟩ := Prod.mk.inj hp
    have h2' : a' 1 = a 1 := congrFun h2 0
    subst h1
    have hs : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun z => rfl
    simp only [hs, g65g_pzc]
    rw [g65g_perm2]
    have : ((x', u, a) = (x', u, a')) ↔ (a 0 = a' 0) := by
      constructor
      · intro h; rw [(Prod.mk.inj (Prod.mk.inj h).2).2]
      · intro h
        have : a = a' := by
          rw [g65g_x2 a, g65g_x2 a', h, h2']
        rw [this]
    by_cases h0 : a 0 = a' 0
    · rw [if_pos h0, if_pos (this.2 h0)]
    · rw [if_neg h0, if_neg (mt this.1 h0)]
  · simp only [hq, if_false, star_zero, zero_mul, Finset.sum_const_zero]
    rw [if_neg]
    intro h
    apply hq
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rw [h1, (Prod.mk.inj h2).2]


def g65g_Tenc : Superop ((Qubits 1 × Qubits 0) × (Unit × Qubits 1)) (Qubits 2 × (Fin 1 × (Qubits 0 × Qubits 0))) :=
  fun ρ => Matrix.of fun o o' => ∑ s : Qubits 1, ∑ a : Qubits 1, ∑ s' : Qubits 1, ∑ a' : Qubits 1,
    g65g_pz o.1 (s 0) (a 0) * g65g_c * ρ ((s, default), ((), a)) ((s', default), ((), a')) *
      (g65g_pz o'.1 (s' 0) (a' 0) * g65g_c)

def g65g_Tali : Superop (Qubits 2 × Fin 1) (Qubits 2) :=
  fun ρ => Matrix.of fun o o' => ρ (o, 0) (o', 0)

def g65g_Tbob : Superop (Qubits 2 × (Unit × (Qubits 1 × (Qubits 0 × Qubits 0)))) (Qubits 1 × (Qubits 0 × Qubits 2)) :=
  fun ρ => Matrix.of fun o o' => ∑ b : Qubits 1, ∑ b' : Qubits 1,
    g65g_pz o.2.2 (o.1 0) (b 0) * ρ (o.2.2, ((), (b, (default, default)))) (o'.2.2, ((), (b', (default, default)))) *
      g65g_pz o'.2.2 (o'.1 0) (b' 0)

lemma g65g_Tperm (x : Qubits 2) (r s : Qubits 1) :
    ∑ b : Qubits 1, g65g_pz x (r 0) (b 0) * g65g_pz x (s 0) (b 0) = if r = s then 1 else 0 := by
  rw [g65g_x2 x, g65g_x1 r, g65g_x1 s]
  generalize x 0 = a, x 1 = b, r 0 = c, s 0 = d
  simp only [g65g_s1, g65g_feq]
  cases a <;> cases b <;> cases c <;> cases d <;> simp [g65g_pz]

lemma g65g_Treorder (F : Qubits 1 → Qubits 1 → Qubits 1 → Qubits 1 → ℂ) :
    ∑ x, ∑ x1, ∑ x2, ∑ x3, F x x1 x2 x3 = ∑ x2, ∑ x3, ∑ x, ∑ x1, F x x1 x2 x3 := by
  calc _ = ∑ x, ∑ x2, ∑ x1, ∑ x3, F x x1 x2 x3 := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x, ∑ x2, ∑ x3, ∑ x1, F x x1 x2 x3 :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x2, ∑ x, ∑ x3, ∑ x1, F x x1 x2 x3 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

def g65g_TV : Fin 1 → Matrix (Qubits 2 × (Fin 1 × (Qubits 0 × Qubits 0))) ((Qubits 1 × Qubits 0) × (Unit × Qubits 1)) ℂ :=
  fun _ o i => g65g_pz o.1 (i.1.1 0) (i.2.2 0) * g65g_c

def g65g_TA : Fin 1 → Matrix (Qubits 2) (Qubits 2 × Fin 1) ℂ :=
  fun _ o i => if i.1 = o then 1 else 0

def g65g_TB : Fin 1 → Matrix (Qubits 1 × (Qubits 0 × Qubits 2)) (Qubits 2 × (Unit × (Qubits 1 × (Qubits 0 × Qubits 0)))) ℂ :=
  fun _ o i => if o.2.2 = i.1 then g65g_pz i.1 (o.1 0) (i.2.2.1 0) else 0

lemma g65g_TV_kraus : IsKrausFamily g65g_TV := by
  unfold IsKrausFamily
  ext ⟨⟨s, u⟩, w, a⟩ ⟨⟨s', u'⟩, w', a'⟩
  obtain rfl : u = u' := Subsingleton.elim _ _
  rw [g65g_x1 s, g65g_x1 s', g65g_x1 a, g65g_x1 a']
  generalize s 0 = a0, s' 0 = b0, a 0 = c0, a' 0 = d0
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_unique, g65g_s2, Fin.sum_univ_one, Matrix.one_apply]
  have hc2 := g65g_c2
  cases a0 <;> cases b0 <;> cases c0 <;> cases d0 <;>
    simp [g65g_TV, g65g_pz, g65g_feq, g65g_cc] <;> (ring_nf; try rw [show g65g_c ^ 2 = 1 / 2 by rw [sq, g65g_c2]]; try norm_num)

lemma g65g_Tenc_eq (ρ : Matrix ((Qubits 1 × Qubits 0) × (Unit × Qubits 1)) ((Qubits 1 × Qubits 0) × (Unit × Qubits 1)) ℂ) :
    g65g_Tenc ρ = krausApply g65g_TV ρ := by
  ext o o'
  rw [g65g_kr]
  simp only [g65g_Tenc, g65g_TV, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_one,
    map_mul, g65g_pzc, g65g_cc]
  congr!

lemma g65g_TA_kraus : IsKrausFamily g65g_TA := by
  unfold IsKrausFamily
  ext ⟨x, m⟩ ⟨x', m'⟩
  obtain rfl : m = m' := Subsingleton.elim _ _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_one, Matrix.one_apply]
  simp [g65g_TA, Prod.ext_iff]

lemma g65g_Tali_eq (ρ : Matrix (Qubits 2 × Fin 1) (Qubits 2 × Fin 1) ℂ) : g65g_Tali ρ = krausApply g65g_TA ρ := by
  ext o o'
  rw [g65g_kr]
  simp [g65g_Tali, g65g_TA, Fintype.sum_prod_type, Finset.sum_ite_eq']

lemma g65g_TB_kraus : IsKrausFamily g65g_TB := by
  unfold IsKrausFamily
  ext ⟨y, w, b, u⟩ ⟨y', w', b', u'⟩
  obtain rfl : u = u' := Subsingleton.elim _ _
  rw [g65g_x2 y, g65g_x2 y', g65g_x1 b, g65g_x1 b']
  generalize y 0 = a0, y 1 = a1, y' 0 = b0, y' 1 = b1, b 0 = c0, b' 0 = d0
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_unique, g65g_s1, g65g_s2, Fin.sum_univ_one, Matrix.one_apply]
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases c0 <;> cases d0 <;>
    simp [g65g_TB, g65g_pz, g65g_veq, g65g_feq] <;> norm_num

lemma g65g_Tbob_eq (ρ : Matrix (Qubits 2 × (Unit × (Qubits 1 × (Qubits 0 × Qubits 0))))
    (Qubits 2 × (Unit × (Qubits 1 × (Qubits 0 × Qubits 0)))) ℂ) :
    g65g_Tbob ρ = krausApply g65g_TB ρ := by
  ext o o'
  rw [g65g_kr]
  simp only [g65g_Tbob, g65g_TB, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_one,
    apply_ite (starRingEnd ℂ), map_zero, g65g_pzc, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have key : ∀ (y : Qubits 2) (b : Qubits 1),
      ((y, (), b, (@default (Qubits 0) Pi.instInhabited), (@default (Qubits 0) Pi.instInhabited)) :
        Qubits 2 × (Unit × (Qubits 1 × (Qubits 0 × Qubits 0)))) = (y, default, b, default, default) :=
    fun y b => Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))))
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  have k1 : ∀ (y : Qubits 2) (b : Qubits 1),
      ((y, (), b, (@default (Qubits 0) Pi.instInhabited), (@default (Qubits 0) Pi.instInhabited)) :
        Qubits 2 × (Unit × (Qubits 1 × (Qubits 0 × Qubits 0)))) =
      (y, (@default Unit _), b, (@default (Qubits 0) Unique.instInhabited), (@default (Qubits 0) Unique.instInhabited)) :=
    fun y b => Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))))
  rw [k1, k1]

abbrev g65g_TP : OneWayCode Unit Unit (Qubits 2) (Qubits 2) (Qubits 2) (TaskInput 1 0) (Qubits 2) (TaskBob 1 0 2) where
  e := 1
  q := 0
  c := 0
  memory := 1
  memoryPositive := by norm_num
  encoder := g65g_Tenc
  aliceDecoder := g65g_Tali
  bobDecoder := g65g_Tbob
  encoderChannel := ⟨1, g65g_TV, by convert g65g_TV_kraus, fun ρ => by convert g65g_Tenc_eq ρ⟩
  aliceChannel := ⟨1, g65g_TA, by convert g65g_TA_kraus, fun ρ => by convert g65g_Tali_eq ρ⟩
  bobChannel := ⟨1, g65g_TB, by convert g65g_TB_kraus, fun ρ => by convert g65g_Tbob_eq ρ⟩

theorem g65g_Tmain :
    ExactConversion (coherentResource 2) 1 0 0 (taskTarget 1 0 2) := by
  refine ⟨g65g_TP, rfl, rfl, rfl, ?_⟩
  funext M
  ext i j
  simp only [aliceMap, idTensorSuperop, transmittedCodeState, g65g_TP, g65g_Tenc, g65g_Tali, g65g_Tbob,
    Matrix.of_apply, initialCodeState, coherentResource, taskTarget]
  simp only [Matrix.of_apply, emptySource, pureDensity, maxEntangled, mul_one]
  have e1 : ∀ x y : Qubits 0, (x = y) = True := fun x y => eq_true (Subsingleton.elim x y)
  simp only [e1, if_true]
  obtain ⟨oA, r, u, oB⟩ := i
  obtain ⟨oA', r', u', oB'⟩ := j
  obtain rfl : u = default := Subsingleton.elim _ _
  obtain rfl : u' = default := Subsingleton.elim _ _
  simp only
  have hc1 : ((Real.sqrt (2 ^ 1) : ℝ) : ℂ)⁻¹ = g65g_c := by simp [g65g_c]
  have hc2 : ((Real.sqrt (2 ^ 2) : ℝ) : ℂ)⁻¹ = g65g_c * g65g_c := by
    rw [g65g_c2, show ((2:ℝ) ^ 2) = 2 * 2 by norm_num, Real.sqrt_mul_self (by norm_num)]; norm_num
  by_cases h : oA = oB ∧ oA' = oB'
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, if_true, hc1, hc2, apply_ite (starRingEnd ℂ), g65g_cc, map_zero, map_mul,
      mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ]
    calc _ = ∑ x2 : Qubits 1, ∑ x3 : Qubits 1,
          (∑ x1 : Qubits 1, g65g_pz oA' (x3 0) (x1 0) * g65g_pz oA' (r' 0) (x1 0)) *
          (∑ x : Qubits 1, g65g_pz oA (r 0) (x 0) * g65g_pz oA (x2 0) (x 0)) *
          (M (x2, default) (x3, default) * (g65g_c * g65g_c * (g65g_c * g65g_c))) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            refine (g65g_Treorder _).trans ?_
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
            ring
      _ = _ := by
            simp only [g65g_Tperm, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
              Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have : (if oA = oB then g65g_c * g65g_c else 0) * (if oA' = oB' then g65g_c * g65g_c else 0) = 0 := by
      rcases not_and_or.1 h with h | h <;> simp [h]
    simp only [h, if_false, mul_zero, zero_mul, Finset.sum_const_zero, hc2, apply_ite (starRingEnd ℂ),
      map_zero, map_mul, g65g_cc]
    rw [this, mul_zero]


abbrev g65g_P : OneWayCode Unit Unit Unit Unit Unit (Qubits 2) (Qubits 2 × Qubits 1) (Qubits 2 × Qubits 1) where
  e := 2
  q := 1
  c := 0
  memory := 8
  memoryPositive := by norm_num
  encoder := g65g_enc
  aliceDecoder := g65g_ali
  bobDecoder := g65g_bob
  encoderChannel := ⟨1, g65g_V, by convert g65g_V_kraus, fun ρ => by convert g65g_enc_eq ρ⟩
  aliceChannel := ⟨1, g65g_A, by convert g65g_A_kraus, fun ρ => by convert g65g_ali_eq ρ⟩
  bobChannel := ⟨1, g65g_B, by convert g65g_B_kraus, fun ρ => by convert g65g_bob_eq ρ⟩

theorem g65g_main2 :
    ExactConversion emptyResource 2 1 0 (coherentTarget 2 1) := by
  refine ⟨g65g_P, rfl, rfl, rfl, ?_⟩
  funext M
  ext i j
  simp only [aliceMap, idTensorSuperop, transmittedCodeState, g65g_P, g65g_enc, g65g_ali, g65g_bob,
    Matrix.of_apply, initialCodeState, emptyResource, forwardResource, coherentTarget, coherentResource]
  simp only [Matrix.of_apply, emptySource, pureDensity, maxEntangled, mul_one, g65g_g8idx]
  have e1 : ∀ x y : Qubits 0, (x = y) = True := fun x y => eq_true (Subsingleton.elim x y)
  simp only [e1, if_true]
  obtain ⟨⟨oA, cA⟩, ⟨oB, cB⟩⟩ := i
  obtain ⟨⟨oA', cA'⟩, ⟨oB', cB'⟩⟩ := j
  have hq1 : ∀ a b : Qubits 1, (a 0 = b 0) = (a = b) := by
    intro a b; rw [g65g_x1 a, g65g_x1 b]; exact (g65g_feq _ _).symm
  simp only [g65g_g8idx, g65g_v2, hq1]
  have hc1 : ((Real.sqrt (2 ^ 1) : ℝ) : ℂ)⁻¹ = g65g_c := by simp [g65g_c]
  have hc2 : ((Real.sqrt (2 ^ 2) : ℝ) : ℂ)⁻¹ = g65g_c * g65g_c := by
    rw [g65g_c2, show ((2:ℝ) ^ 2) = 2 * 2 by norm_num, Real.sqrt_mul_self (by norm_num)]; norm_num
  have key : ∀ x y : Qubits 2, ∑ e : Qubits 1, ∑ q : Qubits 1,
      g65g_pz y (q 0) (e 0) * g65g_pz x (q 0) (e 0) = if x = y then 2 else 0 := g65g_beta
  by_cases h : cA = cB ∧ cA' = cB'
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_true, if_true, hc1, hc2, apply_ite (starRingEnd ℂ), g65g_cc, map_zero, map_mul,
      mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ]
    calc _ = (∑ e : Qubits 1, ∑ q : Qubits 1, g65g_pz oB' (q 0) (e 0) * g65g_pz oA' (q 0) (e 0)) *
          (∑ e : Qubits 1, ∑ q : Qubits 1, g65g_pz oB (q 0) (e 0) * g65g_pz oA (q 0) (e 0)) *
          (M oA oA' * (g65g_c * g65g_c) * (g65g_c * g65g_c) * (g65g_c * g65g_c)) := by
            simp only [Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
            ring
      _ = _ := by
            rw [key, key, g65g_c2]
            by_cases h1 : oA = oB <;> by_cases h2 : oA' = oB' <;> simp [h1, h2] <;> ring
  · have : (if cA = cB then g65g_c else 0) * (if cA' = cB' then g65g_c else 0) = 0 := by
      rcases not_and_or.1 h with h | h <;> simp [h]
    rcases not_and_or.1 h with h' | h' <;>
    simp only [h', and_false, if_false, mul_zero, zero_mul, Finset.sum_const_zero, hc1, apply_ite (starRingEnd ℂ),
      map_zero, map_mul, g65g_cc, this]

theorem solution :
    ExactConversion (coherentResource 2) 1 0 0 (taskTarget 1 0 2) ∧
    ExactConversion emptyResource 2 1 0 (coherentTarget 2 1) := ⟨g65g_Tmain, g65g_main2⟩
