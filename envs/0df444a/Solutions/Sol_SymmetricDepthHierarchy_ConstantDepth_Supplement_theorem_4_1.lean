-- Prove2me | solution 1 for SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T17:24:53.344294+00:00
-- url     : https://prove2.me/submissions/b312628b-71e0-4ff5-a525-017d44a8eedb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Classes
import Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_theorem_4_3

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Circuit

variable {K : Type} [Field K] {n : ℕ} {V : Type} [Fintype V]

lemma eqvAt_iff (C : Circuit K n V) (k : ℕ) (g g' : V) :
    C.eqvAt k g g' ↔ (C.label g = C.label g' ∧ C.height g = k ∧ C.height g' = k ∧
      ∀ j, (hj : j < k) → ∀ h₀ : V, C.height h₀ = j →
        (∑ h ∈ Finset.univ.filter (fun h => C.eqvAt j h h₀), C.mult g h) =
        (∑ h ∈ Finset.univ.filter (fun h => C.eqvAt j h h₀), C.mult g' h)) := by
  rw [eqvAt]

lemma eqvAt_symm (C : Circuit K n V) {k : ℕ} {g g' : V} (h : C.eqvAt k g g') :
    C.eqvAt k g' g := by
  rw [eqvAt_iff] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1.symm, h3, h2, fun j hj h₀ hh => (h4 j hj h₀ hh).symm⟩

lemma eqvAt_trans (C : Circuit K n V) {k : ℕ} {a b c : V} (h : C.eqvAt k a b)
    (h' : C.eqvAt k b c) : C.eqvAt k a c := by
  rw [eqvAt_iff] at h h' ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨k1, k2, k3, k4⟩ := h'
  exact ⟨h1.trans k1, h2, k3, fun j hj h₀ hh => (h4 j hj h₀ hh).trans (k4 j hj h₀ hh)⟩

lemma eqvAt_refl (C : Circuit K n V) (g : V) : C.eqvAt (C.height g) g g := by
  rw [eqvAt_iff]
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

lemma mem_classOf (C : Circuit K n V) (g x : V) :
    x ∈ C.classOf g ↔ C.eqvAt (C.height g) g x := by
  simp [classOf, GateEquiv]

lemma self_mem_classOf (C : Circuit K n V) (g : V) : g ∈ C.classOf g :=
  (C.mem_classOf g g).2 (C.eqvAt_refl g)

lemma height_of_mem_classOf (C : Circuit K n V) {g x : V} (h : x ∈ C.classOf g) :
    C.height x = C.height g := by
  rw [mem_classOf, eqvAt_iff] at h
  exact h.2.2.1

lemma label_of_mem_classOf (C : Circuit K n V) {g x : V} (h : x ∈ C.classOf g) :
    C.label g = C.label x := by
  rw [mem_classOf, eqvAt_iff] at h
  exact h.1

lemma classOf_eq_of_mem (C : Circuit K n V) {g x : V} (h : x ∈ C.classOf g) :
    C.classOf x = C.classOf g := by
  have hh := C.height_of_mem_classOf h
  rw [mem_classOf] at h
  ext y
  rw [mem_classOf, mem_classOf, hh]
  constructor
  · intro hy; exact C.eqvAt_trans h hy
  · intro hy; exact C.eqvAt_trans (C.eqvAt_symm h) hy

lemma rep_mem (C : Circuit K n V) {c : Finset V} (hc : C.IsClass c) : C.rep c ∈ c := by
  obtain ⟨g, rfl⟩ := hc
  have hne : (C.classOf g).Nonempty := ⟨g, C.self_mem_classOf g⟩
  unfold rep
  rw [dif_pos hne]
  exact hne.choose_spec

/-! Heights strictly increase along wires. -/

def DownPath (C : Circuit K n V) : ℕ → V → Prop
  | 0, _ => True
  | k + 1, g => ∃ h, C.Wire h g ∧ DownPath C k h

lemma heightAux_mono (C : Circuit K n V) (k : ℕ) (g : V) :
    C.heightAux k g ≤ C.heightAux (k + 1) g := by
  induction k generalizing g with
  | zero => simp [heightAux]
  | succ k ih =>
    simp only [heightAux]
    apply Finset.sup_mono_fun
    intro h _
    split_ifs
    · exact Nat.add_le_add_right (ih h) 1
    · exact le_rfl

lemma downPath_of_lt (C : Circuit K n V) (k : ℕ) (g : V)
    (hlt : C.heightAux k g < C.heightAux (k + 1) g) : C.DownPath (k + 1) g := by
  induction k generalizing g with
  | zero =>
    simp only [heightAux] at hlt
    obtain ⟨h, _, hh⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset V)
      ⟨g, Finset.mem_univ g⟩ (fun h => if C.Wire h g then (0 : ℕ) + 1 else 0)
    rw [hh] at hlt
    by_cases hw : C.Wire h g
    · exact ⟨h, hw, trivial⟩
    · rw [if_neg hw] at hlt; exact absurd hlt (lt_irrefl 0)
  | succ k ih =>
    have e1 : C.heightAux (k + 1 + 1) g = Finset.univ.sup
        (fun h => if C.Wire h g then C.heightAux (k + 1) h + 1 else 0) := rfl
    have hlt' := hlt
    rw [e1] at hlt'
    obtain ⟨h, _, hh⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset V)
      ⟨g, Finset.mem_univ g⟩ (fun h => if C.Wire h g then C.heightAux (k + 1) h + 1 else 0)
    rw [hh] at hlt'
    by_cases hw : C.Wire h g
    · rw [if_pos hw] at hlt'
      have hle : C.heightAux k h + 1 ≤ C.heightAux (k + 1) g := by
        show _ ≤ Finset.univ.sup (fun h => if C.Wire h g then C.heightAux k h + 1 else 0)
        refine le_trans ?_ (Finset.le_sup (f := fun h => if C.Wire h g then
          C.heightAux k h + 1 else 0) (Finset.mem_univ h))
        simp [hw]
      exact ⟨h, hw, ih h (by omega)⟩
    · rw [if_neg hw] at hlt'; exact absurd hlt' (Nat.not_lt_zero _)

lemma exists_seq_of_downPath (C : Circuit K n V) (k : ℕ) (g : V) (hp : C.DownPath k g) :
    ∃ f : ℕ → V, f 0 = g ∧ ∀ i < k, C.Wire (f (i + 1)) (f i) := by
  induction k generalizing g with
  | zero => exact ⟨fun _ => g, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨h, hw, hp'⟩ := hp
    obtain ⟨f, hf0, hf⟩ := ih h hp'
    refine ⟨fun i => match i with | 0 => g | i + 1 => f i, rfl, ?_⟩
    intro i hi
    cases i with
    | zero => simpa [hf0] using hw
    | succ i => exact hf i (by omega)

lemma not_downPath_card (C : Circuit K n V) (hC : C.WellFormed) (g : V) :
    ¬ C.DownPath (Fintype.card V) g := by
  intro hp
  obtain ⟨f, _, hf⟩ := C.exists_seq_of_downPath _ g hp
  have trans : ∀ m i, i + m + 1 ≤ Fintype.card V →
      Relation.TransGen C.Wire (f (i + m + 1)) (f i) := by
    intro m
    induction m with
    | zero => intro i hi; exact Relation.TransGen.single (hf i (by omega))
    | succ m ih =>
      intro i hi
      have h1 := hf (i + m + 1) (by omega)
      have h2 := ih i (by omega)
      have : i + (m + 1) + 1 = i + m + 1 + 1 := by omega
      rw [this]
      exact Relation.TransGen.head h1 h2
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card V + 1) => f i) (by simp)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · have := trans (b.val - a.val - 1) a.val (by omega)
    have e : a.val + (b.val - a.val - 1) + 1 = b.val := by omega
    rw [e, ← heq] at this
    exact hC.acyclic _ this
  · have := trans (a.val - b.val - 1) b.val (by omega)
    have e : b.val + (a.val - b.val - 1) + 1 = a.val := by omega
    rw [e, heq] at this
    exact hC.acyclic _ this

lemma height_lt_of_wire (C : Circuit K n V) (hC : C.WellFormed) {h g : V}
    (hw : C.Wire h g) : C.height h < C.height g := by
  obtain ⟨M, hM⟩ : ∃ M, Fintype.card V = M + 1 :=
    ⟨Fintype.card V - 1, by have := Fintype.card_pos_iff.2 ⟨h⟩; omega⟩
  have hstab : C.heightAux M h = C.heightAux (M + 1) h := by
    rcases (C.heightAux_mono M h).lt_or_eq with hlt | heq
    · exact absurd (C.downPath_of_lt M h hlt) (by rw [← hM]; exact C.not_downPath_card hC h)
    · exact heq
  unfold height
  rw [hM, ← hstab]
  simp only [heightAux]
  refine lt_of_lt_of_le ?_ (Finset.le_sup (f := fun h' => if C.Wire h' g then
    C.heightAux M h' + 1 else 0) (Finset.mem_univ h))
  simp [hw]

lemma classMult_sum_eq (C : Circuit K n V) (hC : C.WellFormed) {g0 h0 r g x : V}
    (hr : r ∈ C.classOf g0) (hg : g ∈ C.classOf g0) (hx : x ∈ C.classOf h0)
    (hw : C.Wire x r) :
    (∑ y ∈ C.classOf h0, C.mult g y) = ∑ y ∈ C.classOf h0, C.mult r y := by
  have hlt := C.height_lt_of_wire hC hw
  rw [C.height_of_mem_classOf hx, C.height_of_mem_classOf hr] at hlt
  have hset : C.classOf h0 = Finset.univ.filter (fun y => C.eqvAt (C.height h0) y h0) := by
    ext y
    rw [mem_classOf, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ _, C.eqvAt_symm h⟩, fun h => C.eqvAt_symm h.2⟩
  rw [mem_classOf, eqvAt_iff] at hr hg
  rw [hset, ← hg.2.2.2 _ hlt h0 rfl, hr.2.2.2 _ hlt h0 rfl]

/-! Depth of the rigidification. -/

lemma isInput_iff_of_label {V' : Type} [Fintype V'] (C : Circuit K n V) (D : Circuit K n V')
    {a : V} {b : V'} (h : C.label a = D.label b) : C.IsInput a ↔ D.IsInput b := by
  unfold IsInput; rw [h]

lemma inputDepthAux_mono (C : Circuit K n V) (k : ℕ) (g : V) :
    C.inputDepthAux k g ≤ C.inputDepthAux (k + 1) g := by
  induction k generalizing g with
  | zero =>
    simp only [inputDepthAux]
    split_ifs
    · exact le_rfl
    · exact bot_le
  | succ k ih =>
    show (if C.IsInput g then 0 else Finset.univ.sup fun h =>
        if C.Wire h g then C.inputDepthAux k h + 1 else ⊥) ≤
      (if C.IsInput g then 0 else Finset.univ.sup fun h =>
        if C.Wire h g then C.inputDepthAux (k + 1) h + 1 else ⊥)
    split_ifs
    · exact le_rfl
    · apply Finset.sup_mono_fun
      intro h _
      split_ifs
      · exact add_le_add (ih h) le_rfl
      · exact le_rfl

lemma inputDepthAux_le_of_le (C : Circuit K n V) {k m : ℕ} (hkm : k ≤ m) (g : V) :
    C.inputDepthAux k g ≤ C.inputDepthAux m g := by
  induction m, hkm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact ih.trans (C.inputDepthAux_mono m g)

lemma label_rep_of_mem (C : Circuit K n V) {c : Finset V} (hc : C.IsClass c) {g : V}
    (hg : g ∈ c) : C.label (C.rep c) = C.label g := by
  have hr := C.rep_mem hc
  obtain ⟨g0, rfl⟩ := hc
  rw [← C.label_of_mem_classOf hr, C.label_of_mem_classOf hg]

lemma rig_label (C : Circuit K n V) (c : C.RGate) {g : V} (hg : g ∈ c.1) :
    C.rigidification.label c = C.label g :=
  C.label_rep_of_mem c.2.1 hg

lemma exists_wire_of_classMult (C : Circuit K n V) (hC : C.WellFormed) {c d : Finset V}
    (hc : C.IsClass c) (hd : C.IsClass d) {g : V} (hg : g ∈ c)
    (hpos : 0 < ∑ y ∈ d, C.mult (C.rep c) y) : ∃ y ∈ d, C.Wire y g := by
  obtain ⟨x, hx, hxpos⟩ := Finset.exists_lt_of_sum_lt
    (show ∑ y ∈ d, (0 : ℕ) < ∑ y ∈ d, C.mult (C.rep c) y by simpa using hpos)
  have hr := C.rep_mem hc
  obtain ⟨g0, rfl⟩ := hc
  obtain ⟨h0, rfl⟩ := hd
  have heq := C.classMult_sum_eq hC hr hg hx hxpos
  have hpos' : 0 < ∑ y ∈ C.classOf h0, C.mult g y := by
    rw [heq]; exact lt_of_lt_of_le hxpos (Finset.single_le_sum (by simp) hx)
  obtain ⟨y, hy, hypos⟩ := Finset.exists_lt_of_sum_lt
    (show ∑ y ∈ C.classOf h0, (0 : ℕ) < ∑ y ∈ C.classOf h0, C.mult g y by simpa using hpos')
  exact ⟨y, hy, hypos⟩

lemma rig_inputDepthAux_le (C : Circuit K n V) (hC : C.WellFormed) (k : ℕ) :
    ∀ (c : C.RGate) (g : V), g ∈ c.1 →
      C.rigidification.inputDepthAux k c ≤ C.inputDepthAux k g := by
  induction k with
  | zero =>
    intro c g hg
    have hi := C.rigidification.isInput_iff_of_label C (C.rig_label c hg)
    simp only [inputDepthAux]
    by_cases h : C.IsInput g
    · rw [if_pos (hi.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hi.1 h'))]; exact bot_le
  | succ k ih =>
    intro c g hg
    have hi := C.rigidification.isInput_iff_of_label C (C.rig_label c hg)
    show (if C.rigidification.IsInput c then 0 else Finset.univ.sup fun d =>
        if C.rigidification.Wire d c then C.rigidification.inputDepthAux k d + 1 else ⊥) ≤
      (if C.IsInput g then 0 else Finset.univ.sup fun h =>
        if C.Wire h g then C.inputDepthAux k h + 1 else ⊥)
    by_cases h : C.IsInput g
    · rw [if_pos (hi.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hi.1 h')), if_neg h]
      apply Finset.sup_le
      intro d _
      by_cases hw : C.rigidification.Wire d c
      · rw [if_pos hw]
        have hpos : 0 < ∑ y ∈ d.1, C.mult (C.rep c.1) y := hw
        obtain ⟨y, hyd, hwy⟩ := C.exists_wire_of_classMult hC c.2.1 d.2.1 hg hpos
        refine le_trans (add_le_add (ih d y hyd) le_rfl) ?_
        refine le_trans ?_ (Finset.le_sup (f := fun h' => if C.Wire h' g then
          C.inputDepthAux k h' + 1 else ⊥) (Finset.mem_univ y))
        simp [hwy]
      · rw [if_neg hw]; exact bot_le

lemma class_eq_of_mem (C : Circuit K n V) {c c' : Finset V} (hc : C.IsClass c)
    (hc' : C.IsClass c') {x : V} (hx : x ∈ c) (hx' : x ∈ c') : c = c' := by
  obtain ⟨g0, rfl⟩ := hc
  obtain ⟨g1, rfl⟩ := hc'
  rw [← C.classOf_eq_of_mem hx, ← C.classOf_eq_of_mem hx']

lemma card_RGate_le (C : Circuit K n V) : Fintype.card C.RGate ≤ Fintype.card V := by
  apply Fintype.card_le_of_injective (fun c : C.RGate => C.rep c.1)
  intro c c' hcc
  have h1 := C.rep_mem c.2.1
  have h2 := C.rep_mem c'.2.1
  have hcc' : C.rep c.1 = C.rep c'.1 := hcc
  rw [hcc'] at h1
  exact Subtype.ext (C.class_eq_of_mem c.2.1 c'.2.1 h1 h2)

lemma unbotD_mono {a b : WithBot ℕ} (h : a ≤ b) : a.unbotD 0 ≤ b.unbotD 0 := by
  induction a using WithBot.recBotCoe <;> induction b using WithBot.recBotCoe <;> simp_all

lemma rig_depth_le (C : Circuit K n V) (hC : C.WellFormed) :
    C.rigidification.depth ≤ C.depth := by
  unfold depth
  apply unbotD_mono
  refine le_trans (C.rig_inputDepthAux_le hC _ _ C.out (C.self_mem_classOf C.out)) ?_
  exact C.inputDepthAux_le_of_le C.card_RGate_le _

lemma supportChangesAux_le (C : Circuit K n V) (k : ℕ) (g : V) :
    C.supportChangesAux k g ≤ C.inputDepthAux k g := by
  induction k generalizing g with
  | zero => exact le_rfl
  | succ k ih =>
    show (if C.IsInput g then 0 else Finset.univ.sup fun h =>
        if C.Wire h g then C.supportChangesAux k h + (if C.SupportChanging h g then 1 else 0)
        else ⊥) ≤
      (if C.IsInput g then 0 else Finset.univ.sup fun h =>
        if C.Wire h g then C.inputDepthAux k h + 1 else ⊥)
    split_ifs
    · exact le_rfl
    · apply Finset.sup_mono_fun
      intro h _
      by_cases hw : C.Wire h g
      · rw [if_pos hw, if_pos hw]
        refine add_le_add (ih h) ?_
        by_cases hs : C.SupportChanging h g
        · rw [if_pos hs]
        · rw [if_neg hs]; exact zero_le_one
      · rw [if_neg hw, if_neg hw]

lemma rigidSupportDepth_le_depth (C : Circuit K n V) : C.rigidSupportDepth ≤ C.depth := by
  unfold rigidSupportDepth
  split_ifs
  · exact unbotD_mono (C.supportChangesAux_le _ _)
  · exact le_rfl

lemma supportDepth_le_depth (C : Circuit K n V) (hC : C.WellFormed) :
    C.supportDepth ≤ C.depth :=
  (C.rigidification.rigidSupportDepth_le_depth).trans (C.rig_depth_le hC)

end SymmetricDepthHierarchy.ConstantDepth.Circuit

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

open SymmetricDepthHierarchy.ConstantDepth

/-- The one-gate circuit computing `0`. -/
def zeroCircuit (K : Type) [Field K] (n : ℕ) : Circuit K n (Fin 1) where
  label _ := .const 0
  mult _ _ := 0
  out := 0

lemma zeroCircuit_spec (K : Type) [Field K] (n : ℕ) :
    hasCircuit n (0 : MvPolynomial (Fin n × Fin n) K) (fun C => C.maxOrb ≤ 1) := by
  refine ⟨1, zeroCircuit K n, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun _ _ _ => rfl, ?_, fun g g' _ _ _ => Subsingleton.elim g g', fun g => ?_⟩
    · intro g h
      cases h with
      | single h => exact absurd h (lt_irrefl 0)
      | tail _ h => exact absurd h (lt_irrefl 0)
    · have : g = (zeroCircuit K n).out := Subsingleton.elim _ _
      exact this ▸ Relation.ReflTransGen.refl
  · intro γ
    exact ⟨1, fun _ _ => rfl, fun _ => rfl⟩
  · simp [Circuit.Computes, Circuit.value, Circuit.valueAux, Circuit.evalStep, zeroCircuit]
  · unfold Circuit.maxOrb
    apply Finset.sup_le
    intro g _
    exact (Finset.card_le_univ _).trans (by simp)

lemma eventually_pow_le (c : ℕ) : ∃ M : ℕ, ∀ n : ℕ, M ≤ n →
    ((n : ℝ) ^ c) ≤ Real.rpow 2 (Real.rpow n (1 - 1/2)) := by
  have h1 := (isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)).bound
    (c := Real.log 2 / (c + 1)) (by positivity)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 (h1.and (Filter.eventually_gt_atTop 1))
  refine ⟨⌈X⌉₊, fun n hn => ?_⟩
  have hnX : X ≤ (n : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hn)
  obtain ⟨hb, hn1⟩ := hX n hnX
  have hpos : (0 : ℝ) < n := by linarith
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1.le
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg (by positivity)] at hb
  have e1 : (1 : ℝ) - 1/2 = 1/2 := by norm_num
  rw [e1]
  show (n : ℝ) ^ c ≤ (2 : ℝ) ^ ((n : ℝ) ^ (1/2 : ℝ))
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hpos, Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.2
  have hc1 : (0 : ℝ) < c + 1 := by positivity
  calc Real.log n * c ≤ (c + 1) * Real.log n := by nlinarith
    _ ≤ (c + 1) * (Real.log 2 / (c + 1) * (n : ℝ) ^ (1/2 : ℝ)) := by gcongr
    _ = Real.log 2 * (n : ℝ) ^ (1/2 : ℝ) := by field_simp

lemma depth_bound (a n d D : ℕ) (hn : 2 ≤ n) (hd : d ≤ n ^ a)
    (hD : D ≤ 4 * ⌈Real.logb (5/4 : ℝ) (4 * (max 1 d : ℕ))⌉₊ + 4) :
    (D : ℝ) ≤ ((48 + 20 * a : ℕ) : ℝ) * (Real.logb 2 n) ^ 1 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hLdef : Real.log n = Real.logb 2 n * Real.log 2 := by
    rw [Real.logb, div_mul_cancel₀ _ hl2.ne']
  have hL1 : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hn'
  have hm1 : (1 : ℝ) ≤ ((max 1 d : ℕ) : ℝ) := by exact_mod_cast le_max_left 1 d
  have hm2 : ((max 1 d : ℕ) : ℝ) ≤ (n : ℝ) ^ a := by
    have : max 1 d ≤ n ^ a := max_le (Nat.one_le_pow _ _ (by omega)) hd
    exact_mod_cast this
  have hx : Real.log (4 * ((max 1 d : ℕ) : ℝ)) ≤ 2 * Real.log 2 + a * Real.log n := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by linarith) hm2
    rw [Real.log_pow] at this
    linarith
  have hx0 : 0 ≤ Real.log (4 * ((max 1 d : ℕ) : ℝ)) := Real.log_nonneg (by linarith)
  have h54 : (1 : ℝ) / 5 ≤ Real.log (5/4) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 5/4) (by norm_num)
    norm_num at this ⊢; linarith
  have hlogb : Real.logb (5/4) (4 * ((max 1 d : ℕ) : ℝ)) ≤
      5 * (2 * Real.log 2 + a * Real.log n) := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have hlogb0 : 0 ≤ Real.logb (5/4) (4 * ((max 1 d : ℕ) : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hceil := Nat.ceil_lt_add_one hlogb0
  have hD' : (D : ℝ) ≤ 4 * (⌈Real.logb (5/4 : ℝ) (4 * (max 1 d : ℕ))⌉₊ : ℝ) + 4 := by
    exact_mod_cast hD
  have haL : (a : ℝ) * Real.logb 2 n * Real.log 2 ≤ a * Real.logb 2 n := by
    have := mul_nonneg (Nat.cast_nonneg a) (by linarith : (0 : ℝ) ≤ Real.logb 2 n)
    nlinarith
  rw [hLdef] at hlogb
  push_cast
  rw [pow_one]
  nlinarith

lemma orbit_bound (n c m : ℕ) (hn : 1 ≤ n)
    (h : (m : ℝ) ≤ Real.rpow (max ((n ^ c : ℕ) : ℝ) ((n : ℝ) ^ 2)) (3 / (1/2))) :
    m ≤ n ^ (6 * (c + 2)) := by
  have e : (3 : ℝ) / (1/2) = ((6 : ℕ) : ℝ) := by norm_num
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmax : max ((n ^ c : ℕ) : ℝ) ((n : ℝ) ^ 2) ≤ (n : ℝ) ^ (c + 2) := by
    push_cast
    exact max_le (pow_le_pow_right₀ hn' (by omega)) (pow_le_pow_right₀ hn' (by omega))
  have h0 : 0 ≤ max ((n ^ c : ℕ) : ℝ) ((n : ℝ) ^ 2) := le_max_of_le_right (by positivity)
  rw [e] at h
  change (m : ℝ) ≤ (max ((n ^ c : ℕ) : ℝ) ((n : ℝ) ^ 2)) ^ ((6 : ℕ) : ℝ) at h
  rw [Real.rpow_natCast] at h
  have : (m : ℝ) ≤ ((n ^ (6 * (c + 2)) : ℕ) : ℝ) := by
    push_cast
    calc (m : ℝ) ≤ _ := h
      _ ≤ ((n : ℝ) ^ (c + 2)) ^ 6 := pow_le_pow_left₀ h0 hmax 6
      _ = (n : ℝ) ^ (6 * (c + 2)) := by rw [← pow_mul, mul_comm]
  exact_mod_cast this

lemma vac_to_vp (K : Type) [Field K] (p : Family K) (h : p ∈ symVACK K 1) : p ∈ symVP K := by
  obtain ⟨hi, c, N, H⟩ := h
  refine ⟨hi, c, N, fun n h1 hN => ?_⟩
  obtain ⟨m, C, h1, h2, h3, h4, _⟩ := H n h1 hN
  exact ⟨m, C, h1, h2, h3, h4⟩

lemma vp_to_vac (K : Type) [Field K] [CharZero K] (p : Family K) (hp : pFamily p)
    (h : p ∈ symVP K) : p ∈ symVACK K 1 := by
  obtain ⟨hinv, c, N, H⟩ := h
  obtain ⟨a, N0, hdeg⟩ := hp
  obtain ⟨M0, hM0⟩ := eventually_pow_le c
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = max (max N N0) (max M0 2) := ⟨_, rfl⟩
  let p' : Family K := fun n => if M ≤ n then p n else 0
  let s : ℕ → ℕ := fun n => if M ≤ n then n ^ c else 1
  have hinv' : invariantFamily p' := by
    intro n hn γ
    by_cases h : M ≤ n
    · simp only [p', if_pos h]; exact hinv n hn γ
    · simp only [p', if_neg h]; simp
  have hbound : ∀ n, 1 ≤ n → (s n : ℝ) ≤ Real.rpow 2 (Real.rpow n (1 - 1/2)) := by
    intro n hn
    by_cases h : M ≤ n
    · simp only [s, if_pos h]; push_cast; exact hM0 n (le_trans (by omega) h)
    · simp only [s, if_neg h]; push_cast
      exact Real.one_le_rpow (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hcirc : ∀ n, 1 ≤ n → hasCircuit n (p' n) (fun C => C.maxOrb ≤ s n) := by
    intro n hn
    by_cases h : M ≤ n
    · simp only [p', s, if_pos h]; exact H n hn (le_trans (by omega) h)
    · simp only [p', s, if_neg h]; exact zeroCircuit_spec K n
  obtain ⟨N', HN'⟩ := theorem_4_3 K (1/2) (by norm_num) p' (fun n => (p' n).totalDegree) s
    hinv' (fun n _ => le_rfl) hbound hcirc
  refine ⟨hinv, max (6 * (c + 2)) (48 + 20 * a), max N' M, fun n hn hNn => ?_⟩
  have hMn : M ≤ n := le_trans (le_max_right _ _) hNn
  obtain ⟨m, C, hwf, hsym, hcomp, hdepth, horb⟩ := HN' n hn (le_trans (le_max_left _ _) hNn)
  have hpn : p' n = p n := if_pos hMn
  have hsn : s n = n ^ c := if_pos hMn
  refine ⟨m, C, hwf, hsym, hpn ▸ hcomp, ?_, ?_⟩
  · have horb' : (C.maxOrb : ℝ) ≤
        Real.rpow (max ((n ^ c : ℕ) : ℝ) ((n : ℝ) ^ 2)) (3 / (1/2)) := by
      rw [← hsn]; exact horb
    exact (orbit_bound n c _ hn horb').trans
      (Nat.pow_le_pow_right hn (le_max_left _ _))
  · have hd : (p' n).totalDegree ≤ n ^ a := by
      rw [hpn]; exact hdeg n (le_trans (by omega) hMn)
    have h1 := depth_bound a n _ _ (by omega) hd ((C.supportDepth_le_depth hwf).trans hdepth)
    refine h1.trans ?_
    have hL : 0 ≤ (Real.logb 2 n) ^ 1 := by
      rw [pow_one]; exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right _ _) hL

end SymmetricDepthHierarchy.ConstantDepth.Supplement

open SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem solution (K : Type) [Field K] [CharZero K] (p : Family K)
    (hp : pFamily p) : p ∈ symVP K ↔ p ∈ symVACK K 1 :=
  ⟨vp_to_vac K p hp, vac_to_vp K p⟩
