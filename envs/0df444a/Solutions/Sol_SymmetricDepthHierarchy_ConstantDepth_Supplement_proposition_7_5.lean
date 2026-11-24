-- Prove2me | solution 1 for SymmetricDepthHierarchy.ConstantDepth.Supplement.proposition_7_5
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T12:28:59.494864+00:00
-- url     : https://prove2.me/submissions/e8826da1-035d-4530-bace-14c12b6554fa

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Joint

set_option autoImplicit false
open scoped Classical
noncomputable section


namespace SymmetricDepthHierarchy.ConstantDepth.Supplement
namespace VariableCircuit
variable {K X V : Type} [Field K] [Fintype V]

theorem evalStep_congr (C : VariableCircuit K X V) (a b : V → MvPolynomial X K) (v : V)
    (h : ∀ u, 0 < C.mult v u → a u = b u) : C.evalStep a v = C.evalStep b v := by
  unfold evalStep
  cases hl : C.label v with
  | var x => rfl
  | const c => rfl
  | op o =>
    cases o with
    | add =>
      simp only
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : 0 < C.mult v u
      · rw [h u hu]
      · have : C.mult v u = 0 := by omega
        simp [this]
    | mul =>
      simp only
      refine Finset.prod_congr rfl fun u _ => ?_
      by_cases hu : 0 < C.mult v u
      · rw [h u hu]
      · have : C.mult v u = 0 := by omega
        simp [this]

theorem polynomial_eq_of_fixed (C : VariableCircuit K X V)
    (hacyc : ∀ v, ¬ Relation.TransGen C.wire v v)
    (a : V → MvPolynomial X K) (ha : ∀ v, a v = C.evalStep a v) :
    C.polynomial = a C.out := by
  have key : ∀ k v, (Finset.univ.filter fun b => Relation.TransGen C.wire b v).card ≤ k →
      C.evalAux k v = a v := by
    intro k
    induction k with
    | zero =>
      intro v hv
      have hempty : ∀ u, ¬ 0 < C.mult v u := by
        intro u hu
        have : u ∈ Finset.univ.filter fun b => Relation.TransGen C.wire b v :=
          by simp [Relation.TransGen.single (show C.wire u v from hu)]
        have := Finset.card_pos.mpr ⟨u, this⟩
        omega
      rw [ha v]
      exact C.evalStep_congr _ _ v (fun u hu => absurd hu (hempty u))
    | succ k ih =>
      intro v hv
      rw [ha v]
      show C.evalStep (C.evalAux k) v = _
      refine C.evalStep_congr _ _ v fun u hu => ih u ?_
      have hsub : (Finset.univ.filter fun b => Relation.TransGen C.wire b u) ⊂
          (Finset.univ.filter fun b => Relation.TransGen C.wire b v) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨u, by simp [Relation.TransGen.single (show C.wire u v from hu)], ?_⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro h
          exact hacyc u h
        · intro b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
          exact hb.tail (show C.wire u v from hu)
      have := Finset.card_lt_card hsub
      omega
  unfold polynomial
  exact key _ _ (le_trans (Finset.card_le_univ _) le_rfl)


variable {W : Type} [Fintype W]

def reindex (e : V ≃ W) (C : VariableCircuit K X V) : VariableCircuit K X W where
  label w := C.label (e.symm w)
  mult w w' := C.mult (e.symm w) (e.symm w')
  out := e C.out

theorem reindex_transGen (e : V ≃ W) (C : VariableCircuit K X V) (a b : W) :
    Relation.TransGen (C.reindex e).wire a b ↔ Relation.TransGen C.wire (e.symm a) (e.symm b) := by
  constructor
  · intro h
    exact Relation.TransGen.lift e.symm (fun _ _ h => h) a b h
  · intro h
    have := Relation.TransGen.lift (p := (C.reindex e).wire) e (fun x y h => by
      show 0 < C.mult (e.symm (e y)) (e.symm (e x))
      simpa using (show 0 < C.mult y x from h)) _ _ h
    simpa [Function.onFun] using this

theorem reindex_reflTransGen (e : V ≃ W) (C : VariableCircuit K X V) (a b : W) :
    Relation.ReflTransGen (C.reindex e).wire a b ↔ Relation.ReflTransGen C.wire (e.symm a) (e.symm b) := by
  rw [Relation.reflTransGen_iff_eq_or_transGen, Relation.reflTransGen_iff_eq_or_transGen,
    reindex_transGen]
  simp [e.symm.injective.eq_iff]

theorem reindex_wellFormed (e : V ≃ W) (C : VariableCircuit K X V) (h : C.wellFormed) :
    (C.reindex e).wellFormed := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v u hv
    exact h1 _ _ (by simpa [isInput, reindex] using hv)
  · intro v hv
    exact h2 _ ((reindex_transGen e C v v).1 hv)
  · intro u v hu hv hl
    exact e.symm.injective (h3 _ _ (by simpa [isInput, reindex] using hu)
      (by simpa [isInput, reindex] using hv) (by simpa [reindex] using hl))
  · intro v
    have := (reindex_reflTransGen e C v (e C.out)).2 (by simpa using h4 (e.symm v))
    exact this

theorem reindex_evalStep (e : V ≃ W) (C : VariableCircuit K X V) (b : V → MvPolynomial X K) (w : W) :
    (C.reindex e).evalStep (fun w => b (e.symm w)) w = C.evalStep b (e.symm w) := by
  unfold evalStep
  simp only [reindex]
  cases C.label (e.symm w) with
  | var x => rfl
  | const c => rfl
  | op o =>
    cases o with
    | add => exact Fintype.sum_equiv e.symm _ _ (fun u => rfl)
    | mul => exact Fintype.prod_equiv e.symm _ _ (fun u => rfl)

theorem reindex_evalAux (e : V ≃ W) (C : VariableCircuit K X V) (k : ℕ) (w : W) :
    (C.reindex e).evalAux k w = C.evalAux k (e.symm w) := by
  induction k generalizing w with
  | zero => exact reindex_evalStep e C (fun _ => 0) w
  | succ k ih =>
    show (C.reindex e).evalStep ((C.reindex e).evalAux k) w = C.evalStep (C.evalAux k) _
    have : (C.reindex e).evalAux k = fun w => C.evalAux k (e.symm w) := funext ih
    rw [this]
    exact reindex_evalStep e C _ w

theorem reindex_polynomial (e : V ≃ W) (C : VariableCircuit K X V) :
    (C.reindex e).polynomial = C.polynomial := by
  unfold polynomial
  rw [reindex_evalAux]
  simp only [reindex]
  rw [Fintype.card_congr e.symm]
  simp

theorem reindex_symmetric (e : V ≃ W) (C : VariableCircuit K X V) {H : Type} [Group H]
    (ρ : H →* Equiv.Perm X) (h : C.symmetric ρ) : (C.reindex e).symmetric ρ := by
  intro γ
  obtain ⟨σ, h1, h2⟩ := h γ
  refine ⟨e.symm.trans (σ.trans e), ?_, ?_⟩
  · intro u v
    simpa [reindex] using h1 (e.symm u) (e.symm v)
  · intro v
    simpa [reindex] using h2 (e.symm v)

theorem maxOrb_le_card (C : VariableCircuit K X V) {H : Type} [Group H]
    (ρ : H →* Equiv.Perm X) : C.maxOrb ρ ≤ Fintype.card V := by
  unfold maxOrb
  exact Finset.sup_le fun v _ => Finset.card_filter_le _ _ |>.trans (by simp)

end VariableCircuit
end SymmetricDepthHierarchy.ConstantDepth.Supplement


namespace SymmetricDepthHierarchy.ConstantDepth.Supplement
namespace PermCirc

inductive G (n : ℕ)
  | xv (i j : Fin n) | yv (i j : Fin n) | m1 | one
  | my (i j : Fin n) | ny (i j : Fin n) | rt (i j : Fin n) | ct (i j : Fin n)
  | xy (i j : Fin n) | row (i : Fin n) | col (j : Fin n) | tt (i j : Fin n) | out
  deriving DecidableEq, Fintype

variable {n : ℕ}
open G

def isKid : G n → G n → Prop
  | my i j, m1 => True
  | my i j, yv a b => a = i ∧ b = j
  | ny _ _, one => True
  | ny i j, my a b => a = i ∧ b = j
  | rt i j, yv a b => a = i ∧ b = j
  | rt i j, ny a b => a = i ∧ b ≠ j
  | ct i j, yv a b => a = i ∧ b = j
  | ct i j, ny a b => b = j ∧ a ≠ i
  | row i, rt a _ => a = i
  | col j, ct _ b => b = j
  | xy i j, xv a b => a = i ∧ b = j
  | xy i j, yv a b => a = i ∧ b = j
  | tt i j, xy a b => a = i ∧ b = j
  | tt i j, ny a b => a = i ∧ b = j
  | out, row _ => True
  | out, col _ => True
  | out, tt _ _ => True
  | _, _ => False

def rk : G n → ℕ
  | xv _ _ => 0 | yv _ _ => 0 | m1 => 0 | one => 1 | my _ _ => 1 | ny _ _ => 2
  | rt _ _ => 3 | ct _ _ => 3 | xy _ _ => 3 | row _ => 4 | col _ => 4 | tt _ _ => 4 | out => 5

theorem isKid_rk {u v : G n} (h : isKid u v) : rk v < rk u := by
  cases u <;> cases v <;> simp_all [isKid, rk]

def mapG (α β : Equiv.Perm (Fin n)) : G n → G n
  | xv i j => xv (α i) (β j) | yv i j => yv (α i) (β j) | m1 => m1 | one => one
  | my i j => my (α i) (β j) | ny i j => ny (α i) (β j) | rt i j => rt (α i) (β j)
  | ct i j => ct (α i) (β j) | xy i j => xy (α i) (β j) | row i => row (α i)
  | col j => col (β j) | tt i j => tt (α i) (β j) | out => out

theorem mapG_symm (α β : Equiv.Perm (Fin n)) (v : G n) : mapG α.symm β.symm (mapG α β v) = v := by
  cases v <;> simp [mapG]

theorem mapG_symm' (α β : Equiv.Perm (Fin n)) (v : G n) : mapG α β (mapG α.symm β.symm v) = v := by
  cases v <;> simp [mapG]

def mapEquiv (α β : Equiv.Perm (Fin n)) : Equiv.Perm (G n) where
  toFun := mapG α β
  invFun := mapG α.symm β.symm
  left_inv := mapG_symm α β
  right_inv := mapG_symm' α β

theorem isKid_map (α β : Equiv.Perm (Fin n)) (u v : G n) :
    isKid (mapG α β u) (mapG α β v) ↔ isKid u v := by
  cases u <;> cases v <;> simp [isKid, mapG]

theorem mapG_one_m1 (α β : Equiv.Perm (Fin n)) (u v : G n) :
    (mapG α β u = one ∧ mapG α β v = m1) ↔ (u = one ∧ v = m1) := by
  cases u <;> cases v <;> simp [mapG]


def lab (K : Type) [Field K] (n : ℕ) : G n → VariableLabel K ((Fin n × Fin n) ⊕ Fin (n * n))
  | xv i j => .var (.inl (i, j))
  | yv i j => .var (.inr (finProdFinEquiv (i, j)))
  | m1 => .const (-1)
  | ny _ _ => .op .add | row _ => .op .add | col _ => .op .add | tt _ _ => .op .add
  | _ => .op .mul

def circ (K : Type) [Field K] (n : ℕ) : VariableCircuit K ((Fin n × Fin n) ⊕ Fin (n * n)) (G n) where
  label := lab K n
  mult u v := if u = one ∧ v = m1 then 2 else if isKid u v then 1 else 0
  out := out

variable {K : Type} [Field K]

def parent (hn : 0 < n) : G n → G n
  | xv i j => xy i j | yv i j => xy i j | m1 => one | one => ny ⟨0, hn⟩ ⟨0, hn⟩
  | my i j => ny i j | ny i j => tt i j | rt i j => row i | ct i j => col j
  | xy i j => tt i j | row _ => out | col _ => out | tt _ _ => out | out => out

theorem parent_kid (hn : 0 < n) (v : G n) (hv : v ≠ out) :
    (circ K n).wire v (parent hn v) := by
  cases v <;> simp_all [VariableCircuit.wire, circ, parent, isKid]

theorem parent_rk (hn : 0 < n) (v : G n) (hv : v ≠ out) : rk v < rk (parent hn v) := by
  cases v <;> simp_all [parent, rk]

theorem wire_rk {u v : G n} (h : (circ K n).wire u v) : rk u < rk v := by
  unfold VariableCircuit.wire circ at h
  simp only at h
  split_ifs at h with h1 h2
  · obtain ⟨rfl, rfl⟩ := h1; simp [rk]
  · exact isKid_rk h2
  · omega

theorem circ_wellFormed (hn : 0 < n) : (circ K n).wellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v u hv
    cases v <;> simp_all [VariableCircuit.isInput, circ, lab, isKid]
  · intro v hv
    have : ∀ a b, Relation.TransGen (circ K n).wire a b → rk a < rk b := by
      intro a b h
      induction h with
      | single h => exact wire_rk h
      | tail _ h ih => exact ih.trans (wire_rk h)
    exact lt_irrefl _ (this _ _ hv)
  · intro u v hu hv hl
    cases u <;> cases v <;>
      simp_all [VariableCircuit.isInput, circ, lab, Prod.ext_iff, finProdFinEquiv.injective.eq_iff]
  · intro v
    induction h : 5 - rk v using Nat.strong_induction_on generalizing v with
    | _ d ih =>
      by_cases hv : v = out
      · subst hv; exact Relation.ReflTransGen.refl
      · have h1 := parent_kid (K := K) hn v hv
        have h2 := parent_rk hn v hv
        have h3 : ∀ w : G n, rk w ≤ 5 := fun w => by cases w <;> simp [rk]
        have := ih (5 - rk (parent hn v)) (by have := h3 v; have := h3 (parent hn v); omega)
          (parent hn v) rfl
        exact Relation.ReflTransGen.head h1 this


def rho (n : ℕ) : Circuit.Gamma n →* Equiv.Perm (Fin (n * n)) where
  toFun γ := finProdFinEquiv.permCongr (matrixAction n γ)
  map_one' := by ext x; simp [matrixAction]; exact Nat.mod_add_div _ _
  map_mul' γ δ := by ext x; simp [matrixAction, Equiv.permCongr_apply]

theorem circ_symmetric : (circ K n).symmetric (jointAction (rho n)) := by
  intro γ
  refine ⟨mapEquiv γ.1 γ.2, ?_, ?_⟩
  · intro u v
    show (if mapG γ.1 γ.2 u = one ∧ mapG γ.1 γ.2 v = m1 then 2 else
      if isKid (mapG γ.1 γ.2 u) (mapG γ.1 γ.2 v) then 1 else 0) =
      (if u = one ∧ v = m1 then 2 else if isKid u v then 1 else 0)
    simp only [mapG_one_m1, isKid_map]
  · intro v
    cases v <;> simp [circ, lab, mapEquiv, mapG, jointAction, rho, matrixAction] <;> rfl

def code : G n → Fin 13 × Option (Fin n) × Option (Fin n)
  | xv i j => (0, some i, some j) | yv i j => (1, some i, some j) | m1 => (2, none, none)
  | one => (3, none, none) | my i j => (4, some i, some j) | ny i j => (5, some i, some j)
  | rt i j => (6, some i, some j) | ct i j => (7, some i, some j) | xy i j => (8, some i, some j)
  | row i => (9, some i, none) | col j => (10, none, some j) | tt i j => (11, some i, some j)
  | out => (12, none, none)

theorem card_G_le : Fintype.card (G n) ≤ 13 * (n + 1) * (n + 1) := by
  have h : Function.Injective (code : G n → _) := by
    intro a b h
    cases a <;> cases b <;> simp_all [code]
  have := Fintype.card_le_of_injective _ h
  simpa [Fintype.card_prod, Fintype.card_option, mul_assoc] using this

abbrev XY (n : ℕ) := (Fin n × Fin n) ⊕ Fin (n * n)

def Xv (K : Type) [Field K] {n : ℕ} (i j : Fin n) : MvPolynomial (XY n) K :=
  MvPolynomial.X (.inl (i, j))
def Yv (K : Type) [Field K] {n : ℕ} (i j : Fin n) : MvPolynomial (XY n) K :=
  MvPolynomial.X (.inr (finProdFinEquiv (i, j)))

def outKid : Fin n ⊕ Fin n ⊕ (Fin n × Fin n) → G n
  | .inl i => row i | .inr (.inl j) => col j | .inr (.inr p) => tt p.1 p.2

theorem outKid_inj : Function.Injective (outKid : Fin n ⊕ Fin n ⊕ (Fin n × Fin n) → G n) := by
  intro a b h
  rcases a with a | a | a <;> rcases b with b | b | b <;> simp_all [outKid, Prod.ext_iff]

def rowV (K : Type) [Field K] {n : ℕ} (i : Fin n) : MvPolynomial (XY n) K :=
  ∑ j, Yv K i j * ∏ k ∈ Finset.univ.erase j, (1 + MvPolynomial.C (-1) * Yv K i k)
def colV (K : Type) [Field K] {n : ℕ} (j : Fin n) : MvPolynomial (XY n) K :=
  ∑ i, Yv K i j * ∏ k ∈ Finset.univ.erase i, (1 + MvPolynomial.C (-1) * Yv K k j)
def ttV (K : Type) [Field K] {n : ℕ} (i j : Fin n) : MvPolynomial (XY n) K :=
  Xv K i j * Yv K i j + (1 + MvPolynomial.C (-1) * Yv K i j)
def outV (K : Type) [Field K] {n : ℕ} : Fin n ⊕ Fin n ⊕ (Fin n × Fin n) → MvPolynomial (XY n) K
  | .inl i => rowV K i | .inr (.inl j) => colV K j | .inr (.inr p) => ttV K p.1 p.2

def val (K : Type) [Field K] {n : ℕ} : G n → MvPolynomial (XY n) K
  | xv i j => Xv K i j | yv i j => Yv K i j | m1 => MvPolynomial.C (-1) | one => 1
  | my i j => MvPolynomial.C (-1) * Yv K i j
  | ny i j => 1 + MvPolynomial.C (-1) * Yv K i j
  | rt i j => Yv K i j * ∏ k ∈ Finset.univ.erase j, (1 + MvPolynomial.C (-1) * Yv K i k)
  | ct i j => Yv K i j * ∏ k ∈ Finset.univ.erase i, (1 + MvPolynomial.C (-1) * Yv K k j)
  | xy i j => Xv K i j * Yv K i j
  | row i => rowV K i | col j => colV K j | tt i j => ttV K i j
  | out => ∏ s, outV K s


theorem step_add (a : G n → MvPolynomial (XY n) K) (v : G n) (hv : v ≠ one)
    (hl : (circ K n).label v = .op .add) :
    (circ K n).evalStep a v = ∑ u ∈ Finset.univ.filter (isKid v), a u := by
  unfold VariableCircuit.evalStep
  rw [hl]
  simp only [circ, hv, false_and, if_false]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs <;> simp

theorem step_mul (a : G n → MvPolynomial (XY n) K) (v : G n) (hv : v ≠ one)
    (hl : (circ K n).label v = .op .mul) :
    (circ K n).evalStep a v = ∏ u ∈ Finset.univ.filter (isKid v), a u := by
  unfold VariableCircuit.evalStep
  rw [hl]
  simp only [circ, hv, false_and, if_false]
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun u _ => ?_
  split_ifs <;> simp

theorem step_one (a : G n → MvPolynomial (XY n) K) :
    (circ K n).evalStep a one = a m1 ^ 2 := by
  unfold VariableCircuit.evalStep
  have hl : (circ K n).label one = .op .mul := rfl
  rw [hl]
  simp only [circ]
  rw [Finset.prod_eq_single m1]
  · simp
  · intro u _ hu
    have : ¬ isKid (one : G n) u := by cases u <;> simp [isKid]
    simp [hu, this]
  · simp

theorem val_fixed (v : G n) : val K v = (circ K n).evalStep (val K) v := by
  cases v with
  | xv i j => rfl
  | yv i j => rfl
  | m1 => rfl
  | one => rw [step_one]; simp [val]
  | my i j =>
    rw [step_mul _ _ (by simp) rfl]
    have : Finset.univ.filter (isKid (my i j)) = {m1, yv i j} := by
      ext u; cases u <;> simp [isKid, eq_comm]
    rw [this, Finset.prod_pair (by simp)]
    simp [val]
  | ny i j =>
    rw [step_add _ _ (by simp) rfl]
    have : Finset.univ.filter (isKid (ny i j)) = {one, my i j} := by
      ext u; cases u <;> simp [isKid, eq_comm]
    rw [this, Finset.sum_pair (by simp)]
    simp [val]
  | rt i j =>
    rw [step_mul _ _ (by simp) rfl]
    have : Finset.univ.filter (isKid (rt i j)) =
        insert (yv i j) ((Finset.univ.erase j).image (ny i)) := by
      ext u; cases u <;> simp [isKid, eq_comm] <;> tauto
    rw [this, Finset.prod_insert (by simp), Finset.prod_image (by intro a _ b _ h; simpa using h)]
    simp [val]
  | ct i j =>
    rw [step_mul _ _ (by simp) rfl]
    have : Finset.univ.filter (isKid (ct i j)) =
        insert (yv i j) ((Finset.univ.erase i).image (fun k => ny k j)) := by
      ext u; cases u <;> simp [isKid, eq_comm] <;> tauto
    rw [this, Finset.prod_insert (by simp), Finset.prod_image (by intro a _ b _ h; simpa using h)]
    simp [val]
  | xy i j =>
    rw [step_mul _ _ (by simp) rfl]
    have : Finset.univ.filter (isKid (xy i j)) = {xv i j, yv i j} := by
      ext u; cases u <;> simp [isKid, eq_comm]
    rw [this, Finset.prod_pair (by simp)]
    simp [val]
  | tt i j =>
    rw [step_add _ _ (by simp) rfl]
    have : Finset.univ.filter (isKid (tt i j)) = {xy i j, ny i j} := by
      ext u; cases u <;> simp [isKid, eq_comm]
    rw [this, Finset.sum_pair (by simp)]
    simp [val, ttV]
  | row i =>
    rw [step_add _ _ (by simp) rfl]
    have : Finset.univ.filter (isKid (row i)) = Finset.univ.image (rt i) := by
      ext u; cases u <;> simp [isKid, eq_comm]
    rw [this, Finset.sum_image (by intro a _ b _ h; simpa using h)]
    rfl
  | col j =>
    rw [step_add _ _ (by simp) rfl]
    have : Finset.univ.filter (isKid (col j)) = Finset.univ.image (fun i => ct i j) := by
      ext u; cases u <;> simp [isKid, eq_comm]
    rw [this, Finset.sum_image (by intro a _ b _ h; simpa using h)]
    rfl
  | out =>
    rw [step_mul _ _ (by simp) rfl]
    have : Finset.univ.filter (isKid (out : G n)) = Finset.univ.image outKid := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        cases u <;> first
          | exact ⟨.inl _, rfl⟩ | exact ⟨.inr (.inl _), rfl⟩
          | exact ⟨.inr (.inr (_, _)), rfl⟩ | exact False.elim h
      · rintro ⟨s, rfl⟩
        rcases s with s | s | s <;> exact trivial
    rw [this, Finset.prod_image (fun a _ b _ h => outKid_inj h)]
    show (∏ s, outV K s) = ∏ s, val K (outKid s)
    refine Finset.prod_congr rfl fun s _ => ?_
    rcases s with s | s | s <;> rfl

end PermCirc
end SymmetricDepthHierarchy.ConstantDepth.Supplement


namespace PermCircAlg
variable {R : Type} [CommRing R] {n : ℕ}

theorem line_sum (f : Fin n → Bool) :
    ∑ j, (if f j then (1 : R) else 0) * ∏ k ∈ Finset.univ.erase j,
      (1 + -1 * (if f k then (1 : R) else 0)) =
    if ∃ j, f j = true ∧ ∀ k, k ≠ j → f k = false then 1 else 0 := by
  have h1 : ∀ j, (if f j then (1 : R) else 0) * ∏ k ∈ Finset.univ.erase j,
      (1 + -1 * (if f k then (1 : R) else 0)) =
      if (f j = true ∧ ∀ k, k ≠ j → f k = false) then 1 else 0 := by
    intro j
    have h2 : ∀ k, (1 + -1 * (if f k then (1 : R) else 0)) = if f k = false then 1 else 0 := by
      intro k; cases f k <;> simp
    simp only [h2]
    rw [Finset.prod_ite_zero]
    by_cases hj : f j = true
    · simp [hj]
    · simp [hj]
  simp only [h1]
  rw [Finset.sum_boole]
  have hc : (Finset.univ.filter fun j => f j = true ∧ ∀ k, k ≠ j → f k = false).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hne
    have := hb.2 a hne
    simp [ha.1] at this
  by_cases hex : ∃ j, f j = true ∧ ∀ k, k ≠ j → f k = false
  · obtain ⟨j, hj⟩ := hex
    have : (Finset.univ.filter fun j => f j = true ∧ ∀ k, k ≠ j → f k = false).card = 1 := by
      apply le_antisymm hc
      exact Finset.card_pos.mpr ⟨j, by simpa using hj⟩
    rw [if_pos ⟨j, hj⟩]; simp [this]
  · have : (Finset.univ.filter fun j => f j = true ∧ ∀ k, k ≠ j → f k = false).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ hj; exact hex ⟨j, hj⟩
    simp [this, hex]

def Good (b : Fin n → Fin n → Bool) : Prop :=
  (∀ i, ∃ j, b i j = true ∧ ∀ k, k ≠ j → b i k = false) ∧
  (∀ j, ∃ i, b i j = true ∧ ∀ k, k ≠ i → b k j = false)

theorem term_eq (x : Fin n → Fin n → R) (b : Fin n → Fin n → Bool) :
    (∏ i, ∑ j, (if b i j then (1 : R) else 0) * ∏ k ∈ Finset.univ.erase j,
      (1 + -1 * (if b i k then (1 : R) else 0))) *
    ((∏ j, ∑ i, (if b i j then (1 : R) else 0) * ∏ k ∈ Finset.univ.erase i,
      (1 + -1 * (if b k j then (1 : R) else 0))) *
    ∏ p : Fin n × Fin n, (x p.1 p.2 * (if b p.1 p.2 then (1 : R) else 0) +
      (1 + -1 * (if b p.1 p.2 then (1 : R) else 0)))) =
    if Good b then ∏ p : Fin n × Fin n, (if b p.1 p.2 then x p.1 p.2 else 1) else 0 := by
  have h3 : ∀ p : Fin n × Fin n, (x p.1 p.2 * (if b p.1 p.2 then (1 : R) else 0) +
      (1 + -1 * (if b p.1 p.2 then (1 : R) else 0))) = if b p.1 p.2 then x p.1 p.2 else 1 := by
    intro p; cases b p.1 p.2 <;> simp
  simp only [h3, line_sum (fun j => b _ j), line_sum (fun i => b i _)]
  rw [Finset.prod_boole, Finset.prod_boole]
  unfold Good
  by_cases h1 : ∀ i, ∃ j, b i j = true ∧ ∀ k, k ≠ j → b i k = false <;>
  by_cases h2 : ∀ j, ∃ i, b i j = true ∧ ∀ k, k ≠ i → b k j = false <;> simp [h1, h2]

def toB (π : Equiv.Perm (Fin n)) : Fin n → Fin n → Bool := fun a j => decide (π a = j)

theorem good_toB (π : Equiv.Perm (Fin n)) : Good (toB π) := by
  refine ⟨fun i => ⟨π i, by simp [toB], fun k hk => by simp [toB, Ne.symm hk]⟩,
    fun j => ⟨π.symm j, by simp [toB], fun k hk => ?_⟩⟩
  simp only [toB, decide_eq_false_iff_not]
  intro h; apply hk; rw [← h]; simp

theorem sum_good (x : Fin n → Fin n → R) :
    ∑ b : Fin n → Fin n → Bool,
      (if Good b then ∏ p : Fin n × Fin n, (if b p.1 p.2 then x p.1 p.2 else 1) else 0) =
    ∑ π : Equiv.Perm (Fin n), ∏ i, x i (π i) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun π _ => toB π) ?_ ?_ ?_ ?_
  · intro π _; simpa using good_toB π
  · intro π _ π' _ h
    refine Equiv.ext fun i => ?_
    have := congrFun (congrFun h i) (π i)
    simp [toB] at this
    exact this.symm
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨hr, hc⟩ := hb
    choose f hf1 hf2 using hr
    choose g hg1 hg2 using hc
    have hinj : Function.Injective f := by
      intro i i' h
      have e1 : i = g (f i) := by
        by_contra hne; have := hg2 (f i) i hne; rw [hf1 i] at this; simp at this
      have e2 : i' = g (f i') := by
        by_contra hne; have := hg2 (f i') i' hne; rw [hf1 i'] at this; simp at this
      rw [e1, e2, h]
    refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), by simp, ?_⟩
    ext i j
    simp only [toB, Equiv.ofBijective_apply]
    by_cases hj : f i = j
    · subst hj; simp [hf1 i]
    · have := hf2 i j (Ne.symm hj); simp [this, hj]
  · intro π _
    simp only [toB, decide_eq_true_eq]
    rw [← Finset.univ_product_univ, Finset.prod_product]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp

end PermCircAlg

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement
namespace PermCirc
variable {K : Type} [Field K] {n : ℕ}

theorem eval_out (e : Fin (n * n) → Bool) (g : XY n → MvPolynomial (Fin n × Fin n) K)
    (hg1 : ∀ ij, g (.inl ij) = MvPolynomial.X ij)
    (hg2 : ∀ y, g (.inr y) = MvPolynomial.C (if e y then 1 else 0)) :
    MvPolynomial.eval₂Hom MvPolynomial.C g (∏ s, outV K s) =
    (∏ i, ∑ j, (if e (finProdFinEquiv (i, j)) then (1 : MvPolynomial (Fin n × Fin n) K) else 0) *
        ∏ k ∈ Finset.univ.erase j,
      (1 + -1 * (if e (finProdFinEquiv (i, k)) then (1 : MvPolynomial (Fin n × Fin n) K) else 0))) *
    ((∏ j, ∑ i, (if e (finProdFinEquiv (i, j)) then (1 : MvPolynomial (Fin n × Fin n) K) else 0) *
        ∏ k ∈ Finset.univ.erase i,
      (1 + -1 * (if e (finProdFinEquiv (k, j)) then (1 : MvPolynomial (Fin n × Fin n) K) else 0))) *
    ∏ p : Fin n × Fin n, (MvPolynomial.X (p.1, p.2) *
        (if e (finProdFinEquiv (p.1, p.2)) then (1 : MvPolynomial (Fin n × Fin n) K) else 0) +
      (1 + -1 * (if e (finProdFinEquiv (p.1, p.2)) then (1 : MvPolynomial (Fin n × Fin n) K) else 0)))) := by
  have hY : ∀ i j : Fin n, MvPolynomial.eval₂Hom MvPolynomial.C g (Yv K i j) =
      (if e (finProdFinEquiv (i, j)) then (1 : MvPolynomial (Fin n × Fin n) K) else 0) := by
    intro i j
    simp only [Yv, MvPolynomial.eval₂Hom_X', hg2]
    split_ifs <;> simp
  have hX : ∀ i j : Fin n, MvPolynomial.eval₂Hom MvPolynomial.C g (Xv K i j) =
      MvPolynomial.X (i, j) := by
    intro i j
    simp [Xv, hg1]
  simp only [outV, rowV, colV, ttV, map_prod, map_sum, map_mul, map_add, map_one, hY, hX,
    Fintype.prod_sum_type, map_neg]

end PermCirc

theorem permanent_eq (K : Type) [Field K] (n : ℕ) :
    booleanSum (K := K) (Y := Fin (n * n)) (n := n) (∏ s, PermCirc.outV K s) =
      permanentFamily K n := by
  let eqv : (Fin (n * n) → Bool) ≃ (Fin n → Fin n → Bool) :=
    (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)
  let F : (Fin n → Fin n → Bool) → MvPolynomial (Fin n × Fin n) K := fun b =>
    if PermCircAlg.Good b then ∏ p : Fin n × Fin n,
      (if b p.1 p.2 then (MvPolynomial.X (p.1, p.2) : MvPolynomial (Fin n × Fin n) K) else 1)
    else 0
  calc booleanSum (K := K) (Y := Fin (n * n)) (n := n) (∏ s, PermCirc.outV K s)
      = ∑ e : Fin (n * n) → Bool, F (eqv e) :=
        Finset.sum_congr (by convert rfl) fun e _ =>
          (PermCirc.eval_out e _ (fun _ => rfl) (fun _ => rfl)).trans
            (PermCircAlg.term_eq (R := MvPolynomial (Fin n × Fin n) K)
              (fun i j => MvPolynomial.X (i, j)) (eqv e))
    _ = ∑ b, F b := Fintype.sum_equiv eqv _ _ (fun _ => rfl)
    _ = ∑ π : Equiv.Perm (Fin n), ∏ i, (MvPolynomial.X (i, π i) : MvPolynomial (Fin n × Fin n) K) :=
        PermCircAlg.sum_good (R := MvPolynomial (Fin n × Fin n) K) (fun i j => MvPolynomial.X (i, j))
    _ = permanentFamily K n := by
        unfold permanentFamily permanent
        exact Finset.sum_congr (by convert rfl) (fun _ _ => rfl)

theorem perm_mem (K : Type) [Field K] : permanentFamily K ∈ symVNP K := by
  refine ⟨fun n => n * n, ⟨2, 0, fun n _ => by simp [sq]⟩, 4, 8, fun n hn => ?_⟩
  have hn0 : 0 < n := hn
  refine ⟨PermCirc.rho n, Fintype.card (PermCirc.G n),
    (PermCirc.circ K n).reindex (Fintype.equivFin _), ?_, ?_, ?_, ?_⟩
  · exact VariableCircuit.reindex_wellFormed _ _ (PermCirc.circ_wellFormed hn0)
  · exact VariableCircuit.reindex_symmetric _ _ _ PermCirc.circ_symmetric
  · rw [VariableCircuit.reindex_polynomial,
      VariableCircuit.polynomial_eq_of_fixed _ (PermCirc.circ_wellFormed hn0).2.1 (PermCirc.val K)
        PermCirc.val_fixed]
    exact permanent_eq K n
  · intro hN
    refine (VariableCircuit.maxOrb_le_card _ _).trans ?_
    simp only [Fintype.card_fin]
    refine PermCirc.card_G_le.trans ?_
    have h8 : 8 ≤ n := hN
    have h1 : n + 1 ≤ 2 * n := by omega
    have h2 : 13 * (n + 1) * (n + 1) ≤ 13 * (2 * n) * (2 * n) := by gcongr
    have h3 : 52 * (n * n) ≤ n * n * (n * n) := Nat.mul_le_mul_right _ (by nlinarith)
    calc 13 * (n + 1) * (n + 1) ≤ 13 * (2 * n) * (2 * n) := h2
      _ = 52 * (n * n) := by ring
      _ ≤ n * n * (n * n) := h3
      _ = n ^ 4 := by ring

end SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem solution (K : Type) [Field K] :
    SymmetricDepthHierarchy.ConstantDepth.Supplement.permanentFamily K ∈
      SymmetricDepthHierarchy.ConstantDepth.Supplement.symVNP K :=
  SymmetricDepthHierarchy.ConstantDepth.Supplement.perm_mem K
