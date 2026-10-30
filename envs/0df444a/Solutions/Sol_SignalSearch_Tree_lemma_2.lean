-- Prove2me | solution 1 for SignalSearch.Tree.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:55:52.377081+00:00
-- url     : https://prove2.me/submissions/abd8bd8b-50cc-492a-9c75-315407e8c69c

import Mathlib
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame
import Definitions.Def_SignalSearch_Tree_Model

namespace SignalSearch.Tree.T7Aux
open SignalSearch.Tree ZeroSumLP.DantzigExt

/-! ### Generic matrix-game assembly -/

theorem assemble {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ)
    (x : κ → ℝ) (y : ι → ℝ) (V : ℝ)
    (hx0 : 0 ≤ x) (hx1 : ∑ j, x j = 1) (hy0 : 0 ≤ y) (hy1 : ∑ i, y i = 1)
    (hAx : ∀ i, ∑ j, A i j * x j ≤ V) (hyA : ∀ j, V ≤ ∑ i, y i * A i j) :
    IsMinMaxStrategy A x V ∧ IsMaxMinStrategy A y V := by
  have key : ∀ (x' : κ → ℝ) (y' : ι → ℝ),
      ∑ j, x' j * ∑ i, y' i * A i j = ∑ i, y' i * ∑ j, A i j * x' j := by
    intro x' y'
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine ⟨⟨⟨hx0, hx1, fun i => hAx i⟩, ?_⟩, ⟨⟨hy0, hy1, fun j => hyA j⟩, ?_⟩⟩
  · rintro x' v' ⟨hx'0, hx'1, hAx'⟩
    have h1 : V ≤ ∑ j, x' j * ∑ i, y i * A i j := by
      calc V = ∑ j, x' j * V := by rw [← Finset.sum_mul, hx'1, one_mul]
        _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hyA j) (hx'0 j)
    have h2 : ∑ i, y i * ∑ j, A i j * x' j ≤ v' := by
      calc _ ≤ ∑ i, y i * v' := Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (hAx' i) (hy0 i)
        _ = v' := by rw [← Finset.sum_mul, hy1, one_mul]
    rw [key] at h1; linarith
  · rintro y' u' ⟨hy'0, hy'1, hyA'⟩
    have h1 : u' ≤ ∑ i, y' i * ∑ j, A i j * x j := by
      calc u' = ∑ j, x j * u' := by rw [← Finset.sum_mul, hx1, one_mul]
        _ ≤ ∑ j, x j * ∑ i, y' i * A i j :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hyA' j) (hx0 j)
        _ = _ := key x y'
    have h2 : ∑ i, y' i * ∑ j, A i j * x j ≤ V := by
      calc _ ≤ ∑ i, y' i * V := Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (hAx i) (hy'0 i)
        _ = V := by rw [← Finset.sum_mul, hy'1, one_mul]
    linarith

/-! ### Sums over leaves -/

theorem sum_leaf_arc (ℓ : ℝ) (f : Leaf (.arc ℓ) → ℝ) : ∑ v, f v = f (.tip ℓ) := by
  rw [Fintype.sum_equiv (Leaf.equivArc ℓ) f (fun _ => f (.tip ℓ))]
  · simp
  · intro v; cases v; rfl

theorem sum_leaf_cons (ℓ : ℝ) (t : RTree) (f : Leaf (.cons ℓ t) → ℝ) :
    ∑ v, f v = ∑ v, f (.down ℓ v) := by
  exact Fintype.sum_equiv (Leaf.equivCons ℓ t) f _ (fun v => by cases v; rfl)

theorem sum_leaf_fork (t₁ t₂ : RTree) (f : Leaf (.fork t₁ t₂) → ℝ) :
    ∑ v, f v = ∑ v, f (.left t₂ v) + ∑ v, f (.right t₁ v) := by
  rw [Fintype.sum_equiv (Leaf.equivFork t₁ t₂) f
    (fun o => match o with | .inl v => f (.left t₂ v) | .inr v => f (.right t₁ v))
    (fun v => by cases v <;> rfl)]
  exact Fintype.sum_sum_type _

/-! ### Products over branch nodes and sums over pure strategies -/

theorem prod_bnode_arc (ℓ : ℝ) (f : BNode (.arc ℓ) → ℝ) : ∏ j, f j = 1 :=
  Finset.prod_of_isEmpty _

theorem prod_bnode_cons (ℓ : ℝ) (t : RTree) (f : BNode (.cons ℓ t) → ℝ) :
    ∏ j, f j = ∏ j, f (.down ℓ j) :=
  Fintype.prod_equiv (BNode.equivCons ℓ t) f _ (fun j => by cases j; rfl)

theorem prod_bnode_fork (t₁ t₂ : RTree) (f : BNode (.fork t₁ t₂) → ℝ) :
    ∏ j, f j = f (.root t₁ t₂) * ((∏ j, f (.left t₂ j)) * ∏ j, f (.right t₁ j)) := by
  rw [Fintype.prod_equiv (BNode.equivFork t₁ t₂) f
    (fun o => match o with
      | none => f (.root t₁ t₂)
      | some (.inl j) => f (.left t₂ j)
      | some (.inr j) => f (.right t₁ j))
    (fun j => by cases j <;> rfl)]
  rw [Fintype.prod_option, Fintype.prod_sum_type]

/-- Gluing pure strategies at a fork. -/
def glue {t₁ t₂ : RTree} (a : Action) (s₁ : SPure t₁) (s₂ : SPure t₂) :
    SPure (.fork t₁ t₂)
  | .root _ _ => a
  | .left _ j => s₁ j
  | .right _ j => s₂ j

def forkEquiv (t₁ t₂ : RTree) : SPure (.fork t₁ t₂) ≃ Action × SPure t₁ × SPure t₂ where
  toFun s := (s (.root t₁ t₂), fun j => s (.left t₂ j), fun j => s (.right t₁ j))
  invFun x := glue x.1 x.2.1 x.2.2
  left_inv s := by funext j; cases j <;> rfl
  right_inv x := by rcases x with ⟨a, s₁, s₂⟩; rfl

def consGlue {ℓ : ℝ} {t : RTree} (s : SPure t) : SPure (.cons ℓ t)
  | .down _ j => s j

def consEquiv (ℓ : ℝ) (t : RTree) : SPure (.cons ℓ t) ≃ SPure t where
  toFun s := fun j => s (.down ℓ j)
  invFun s := consGlue s
  left_inv s := by funext j; cases j; rfl
  right_inv s := rfl

theorem sum_spure_fork (t₁ t₂ : RTree) (F : SPure (.fork t₁ t₂) → ℝ) :
    ∑ s, F s = ∑ a : Action, ∑ s₁ : SPure t₁, ∑ s₂ : SPure t₂, F (glue a s₁ s₂) := by
  rw [Fintype.sum_equiv (forkEquiv t₁ t₂) F (fun x => F (glue x.1 x.2.1 x.2.2))
    (fun s => congrArg F ((forkEquiv t₁ t₂).left_inv s).symm)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]

theorem sum_spure_cons (ℓ : ℝ) (t : RTree) (F : SPure (.cons ℓ t) → ℝ) :
    ∑ s, F s = ∑ s : SPure t, F (consGlue s) :=
  Fintype.sum_equiv (consEquiv ℓ t) F (fun s => F (consGlue s))
    (fun s => congrArg F ((consEquiv ℓ t).left_inv s).symm)


theorem sum_action (F : Action → ℝ) :
    ∑ a, F a = F (fun _ => false) + F id + (F not + F (fun _ => true)) := by
  let e : Action ≃ Bool × Bool :=
    { toFun := fun a => (a false, a true)
      invFun := fun x b => if b then x.2 else x.1
      left_inv := fun a => by funext b; cases b <;> rfl
      right_inv := fun x => rfl }
  rw [Fintype.sum_equiv e F (fun x => F (fun b => if b then x.2 else x.1))
    (fun a => congrArg F (e.left_inv a).symm)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  have h1 : (fun b : Bool => if b then true else true) = fun _ => true := by funext b; cases b <;> rfl
  have h2 : (fun b : Bool => if b then false else true) = not := by funext b; cases b <;> rfl
  have h3 : (fun b : Bool => if b then true else false) = id := by funext b; cases b <;> rfl
  have h4 : (fun b : Bool => if b then false else false) = fun _ => false := by
    funext b; cases b <;> rfl
  rw [h1, h2, h3, h4]; ring

theorem triple_left {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (N : α → ℝ) (X : β → ℝ) (Y : γ → ℝ) (c : α → ℝ) (g : β → ℝ)
    (hX : ∑ b, X b = 1) (hY : ∑ b, Y b = 1) :
    ∑ a, ∑ b, ∑ d, N a * (X b * Y d) * (c a + g b) =
      (∑ a, N a * c a) * 1 + (∑ a, N a) * (∑ b, X b * g b) := by
  have : ∀ a b d, N a * (X b * Y d) * (c a + g b) =
      (N a * c a) * X b * Y d + N a * (X b * g b) * Y d := fun a b d => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hX, hY, mul_one]

theorem triple_right {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (N : α → ℝ) (X : β → ℝ) (Y : γ → ℝ) (c : α → ℝ) (g : γ → ℝ)
    (hX : ∑ b, X b = 1) (hY : ∑ b, Y b = 1) :
    ∑ a, ∑ b, ∑ d, N a * (X b * Y d) * (c a + g d) =
      (∑ a, N a * c a) * 1 + (∑ a, N a) * (∑ d, Y d * g d) := by
  have : ∀ a b d, N a * (X b * Y d) * (c a + g d) =
      (N a * c a) * X b * Y d + N a * X b * (Y d * g d) := fun a b d => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hX, hY, mul_one]

theorem triple_one {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (N : α → ℝ) (X : β → ℝ) (Y : γ → ℝ) :
    ∑ a, ∑ b, ∑ d, N a * (X b * Y d) = (∑ a, N a) * ((∑ b, X b) * ∑ d, Y d) := by
  simp only [← Finset.mul_sum, ← Finset.sum_mul]


/-! ### The Hider distribution -/

/-- Weight of branch 1 at a fork (Definition 4). -/
noncomputable def w1 (p : ℝ) (t₁ t₂ : RTree) : ℝ :=
  if meanDepth p t₂ ≤ meanDepth p t₁ then
    p * t₁.length / (p * t₁.length + (1 - p) * t₂.length)
  else
    (1 - p) * t₁.length / (p * t₂.length + (1 - p) * t₁.length)

/-- Weight of branch 2 at a fork (Definition 4). -/
noncomputable def w2 (p : ℝ) (t₁ t₂ : RTree) : ℝ :=
  if meanDepth p t₂ ≤ meanDepth p t₁ then
    (1 - p) * t₂.length / (p * t₁.length + (1 - p) * t₂.length)
  else
    p * t₂.length / (p * t₂.length + (1 - p) * t₁.length)

theorem hiderDist_left (p : ℝ) (t₁ t₂ : RTree) (v : Leaf t₁) :
    hiderDist p (.fork t₁ t₂) (.left t₂ v) = w1 p t₁ t₂ * hiderDist p t₁ v := rfl

theorem hiderDist_right (p : ℝ) (t₁ t₂ : RTree) (v : Leaf t₂) :
    hiderDist p (.fork t₁ t₂) (.right t₁ v) = w2 p t₁ t₂ * hiderDist p t₂ v := rfl

theorem hiderDist_down (p ℓ : ℝ) (t : RTree) (v : Leaf t) :
    hiderDist p (.cons ℓ t) (.down ℓ v) = hiderDist p t v := rfl

theorem w_facts {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) (t₁ t₂ : RTree)
    (h₁ : 0 < t₁.length) (h₂ : 0 < t₂.length) :
    0 ≤ w1 p t₁ t₂ ∧ 0 ≤ w2 p t₁ t₂ ∧ w1 p t₁ t₂ + w2 p t₁ t₂ = 1 := by
  have hq : 0 ≤ 1 - p := by linarith
  unfold w1 w2
  split_ifs with h
  · have hS : 0 < p * t₁.length + (1 - p) * t₂.length := by nlinarith
    refine ⟨by positivity, by positivity, ?_⟩
    rw [← add_div, div_self hS.ne']
  · have hS : 0 < p * t₂.length + (1 - p) * t₁.length := by nlinarith
    refine ⟨by positivity, by positivity, ?_⟩
    rw [← add_div, add_comm ((1 - p) * t₁.length), div_self hS.ne']

theorem meanDepth_arc (p ℓ : ℝ) : meanDepth p (.arc ℓ) = ℓ := by
  unfold meanDepth meanDepthWrt
  rw [sum_leaf_arc]; simp [hiderDist, depth]

theorem meanDepth_cons_aux (p ℓ : ℝ) (t : RTree) :
    meanDepth p (.cons ℓ t) = ℓ * ∑ v, hiderDist p t v + meanDepth p t := by
  unfold meanDepth meanDepthWrt
  rw [sum_leaf_cons, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hiderDist_down]; simp only [depth]; ring

theorem meanDepth_fork (p : ℝ) (t₁ t₂ : RTree) :
    meanDepth p (.fork t₁ t₂) = w1 p t₁ t₂ * meanDepth p t₁ + w2 p t₁ t₂ * meanDepth p t₂ := by
  unfold meanDepth meanDepthWrt
  rw [sum_leaf_fork, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun v _ => ?_
  · rw [hiderDist_left]; simp only [depth]; ring
  · rw [hiderDist_right]; simp only [depth]; ring

theorem hider_facts {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) :
    ∀ t : RTree, t.PosLengths → 0 < t.length ∧ (∀ v, 0 ≤ hiderDist p t v) ∧
      ∑ v, hiderDist p t v = 1 ∧ 0 ≤ meanDepth p t ∧ meanDepth p t ≤ t.length := by
  intro t
  induction t with
  | arc ℓ =>
    intro ht
    simp only [RTree.PosLengths] at ht
    refine ⟨ht, fun v => show (0:ℝ) ≤ 1 by norm_num, by rw [sum_leaf_arc]; rfl, ?_, ?_⟩
    · rw [meanDepth_arc]; exact ht.le
    · rw [meanDepth_arc]; exact le_refl _
  | cons ℓ t ih =>
    intro ht
    simp only [RTree.PosLengths] at ht
    obtain ⟨h0, h1, h2, h3, h4⟩ := ih ht.2
    refine ⟨by simp only [RTree.length]; linarith, ?_, ?_, ?_, ?_⟩
    · intro v; cases v; exact h1 _
    · rw [sum_leaf_cons]; exact h2
    · rw [meanDepth_cons_aux, h2]; linarith
    · rw [meanDepth_cons_aux, h2]; simp only [RTree.length]; linarith
  | fork t₁ t₂ ih₁ ih₂ =>
    intro ht
    simp only [RTree.PosLengths] at ht
    obtain ⟨a0, a1, a2, a3, a4⟩ := ih₁ ht.1
    obtain ⟨b0, b1, b2, b3, b4⟩ := ih₂ ht.2
    obtain ⟨hw1, hw2, hw⟩ := w_facts hp hp1 t₁ t₂ a0 b0
    refine ⟨by simp only [RTree.length]; linarith, ?_, ?_, ?_, ?_⟩
    · intro v; cases v with
      | left _ v => rw [hiderDist_left]; exact mul_nonneg hw1 (a1 v)
      | right _ v => rw [hiderDist_right]; exact mul_nonneg hw2 (b1 v)
    · rw [sum_leaf_fork]
      simp only [hiderDist_left, hiderDist_right, ← Finset.mul_sum, a2, b2]; linarith
    · rw [meanDepth_fork]; positivity
    · rw [meanDepth_fork]; simp only [RTree.length]; nlinarith


/-! ### The value formula -/

/-- `V(Q) = 2qμ + (p − q)D_Q`. -/
noncomputable def Vt (p : ℝ) (t : RTree) : ℝ :=
  2 * (1 - p) * t.length + (p - (1 - p)) * meanDepth p t

theorem wf_fav1 {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) (a : Action) :
    0 ≤ p * wrongFirst p a false + (1 - p) * wrongFirst p a true - (1 - p) := by
  unfold wrongFirst
  cases h1 : a false <;> cases h2 : a true <;> simp [h1, h2] <;> nlinarith

theorem wf_fav2 {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) (a : Action) :
    0 ≤ (1 - p) * wrongFirst p a false + p * wrongFirst p a true - (1 - p) := by
  unfold wrongFirst
  cases h1 : a false <;> cases h2 : a true <;> simp [h1, h2] <;> nlinarith

theorem alg_hider (p μ₁ μ₂ D₁ D₂ w₁ w₂ c₁ c₂ K α γ : ℝ)
    (e1 : w₁ * μ₂ = α * K) (e2 : w₂ * μ₁ = γ * K) (e3 : w₁ + w₂ = 1) (eαγ : α + γ = 1)
    (hK : 0 ≤ K) (hc : 0 ≤ α * c₁ + γ * c₂ - (1 - p)) :
    2 * (1 - p) * (μ₁ + μ₂) + (p - (1 - p)) * (w₁ * D₁ + w₂ * D₂) ≤
      w₁ * (c₁ * (2 * μ₂) + (2 * (1 - p) * μ₁ + (p - (1 - p)) * D₁)) +
        w₂ * (c₂ * (2 * μ₁) + (2 * (1 - p) * μ₂ + (p - (1 - p)) * D₂)) := by
  have key : w₁ * (c₁ * (2 * μ₂) + (2 * (1 - p) * μ₁ + (p - (1 - p)) * D₁)) +
        w₂ * (c₂ * (2 * μ₁) + (2 * (1 - p) * μ₂ + (p - (1 - p)) * D₂)) -
      (2 * (1 - p) * (μ₁ + μ₂) + (p - (1 - p)) * (w₁ * D₁ + w₂ * D₂)) =
      2 * K * (α * c₁ + γ * c₂ - (1 - p)) := by
    linear_combination (2 * c₁ - 2 * (1 - p)) * e1 + (2 * c₂ - 2 * (1 - p)) * e2 +
      2 * (1 - p) * (μ₁ + μ₂) * e3 - 2 * (1 - p) * K * eαγ
  nlinarith [mul_nonneg hK hc]

theorem hider_ge {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) :
    ∀ t : RTree, t.PosLengths → ∀ s : SPure t,
      Vt p t ≤ ∑ v, hiderDist p t v * time p t s v := by
  intro t
  induction t with
  | arc ℓ =>
    intro ht s
    rw [sum_leaf_arc]
    show _ ≤ 1 * ℓ
    unfold Vt; rw [meanDepth_arc]; simp only [RTree.length]; linarith
  | cons ℓ t ih =>
    intro ht s
    simp only [RTree.PosLengths] at ht
    obtain ⟨-, -, h2, -, -⟩ := hider_facts hp hp1 t ht.2
    have := ih ht.2 (fun j => s (.down ℓ j))
    rw [sum_leaf_cons]
    have e : ∀ v : Leaf t, hiderDist p (.cons ℓ t) (.down ℓ v) * time p (.cons ℓ t) s (.down ℓ v)
        = ℓ * hiderDist p t v + hiderDist p t v * time p t (fun j => s (.down ℓ j)) v := by
      intro v; rw [hiderDist_down]; simp only [time]; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h2]
    unfold Vt at this ⊢
    rw [meanDepth_cons_aux, h2]; simp only [RTree.length]; linarith
  | fork t₁ t₂ ih₁ ih₂ =>
    intro ht s
    simp only [RTree.PosLengths] at ht
    obtain ⟨a0, -, a2, -, -⟩ := hider_facts hp hp1 t₁ ht.1
    obtain ⟨b0, -, b2, -, -⟩ := hider_facts hp hp1 t₂ ht.2
    obtain ⟨hw1, hw2, hw⟩ := w_facts hp hp1 t₁ t₂ a0 b0
    have i1 := ih₁ ht.1 (fun j => s (.left t₂ j))
    have i2 := ih₂ ht.2 (fun j => s (.right t₁ j))
    rw [sum_leaf_fork]
    set a := s (.root t₁ t₂)
    have e1 : ∀ v : Leaf t₁, hiderDist p (.fork t₁ t₂) (.left t₂ v) *
        time p (.fork t₁ t₂) s (.left t₂ v) = w1 p t₁ t₂ * (wrongFirst p a false * (2 * t₂.length)
          * hiderDist p t₁ v + hiderDist p t₁ v * time p t₁ (fun j => s (.left t₂ j)) v) := by
      intro v; rw [hiderDist_left]; simp only [time]; ring
    have e2 : ∀ v : Leaf t₂, hiderDist p (.fork t₁ t₂) (.right t₁ v) *
        time p (.fork t₁ t₂) s (.right t₁ v) = w2 p t₁ t₂ * (wrongFirst p a true * (2 * t₁.length)
          * hiderDist p t₂ v + hiderDist p t₂ v * time p t₂ (fun j => s (.right t₁ j)) v) := by
      intro v; rw [hiderDist_right]; simp only [time]; ring
    simp only [e1, e2, ← Finset.mul_sum, Finset.sum_add_distrib, a2, b2, mul_one]
    have step : Vt p (.fork t₁ t₂) ≤
        w1 p t₁ t₂ * (wrongFirst p a false * (2 * t₂.length) + Vt p t₁) +
        w2 p t₁ t₂ * (wrongFirst p a true * (2 * t₁.length) + Vt p t₂) := by
      unfold Vt; rw [meanDepth_fork]; simp only [RTree.length]
      have hq : 0 ≤ 1 - p := by linarith
      by_cases h : meanDepth p t₂ ≤ meanDepth p t₁
      · have hS : 0 < p * t₁.length + (1 - p) * t₂.length := by nlinarith
        refine alg_hider p _ _ _ _ _ _ _ _ (t₁.length * t₂.length /
          (p * t₁.length + (1 - p) * t₂.length)) p (1 - p) ?_ ?_ hw (by ring)
          (by positivity) (wf_fav1 hp hp1 a)
        · simp only [w1, if_pos h]; ring
        · simp only [w2, if_pos h]; ring
      · have hS : 0 < p * t₂.length + (1 - p) * t₁.length := by nlinarith
        refine alg_hider p _ _ _ _ _ _ _ _ (t₁.length * t₂.length /
          (p * t₂.length + (1 - p) * t₁.length)) (1 - p) p ?_ ?_ hw (by ring)
          (by positivity) (wf_fav2 hp hp1 a)
        · simp only [w1, if_neg h]; ring
        · simp only [w2, if_neg h]; ring
    refine step.trans ?_
    have := mul_le_mul_of_nonneg_left i1 hw1
    have := mul_le_mul_of_nonneg_left i2 hw2
    nlinarith


/-! ### The favoring-bias Searcher strategy -/

theorem fav_arc (p ℓ : ℝ) (s : SPure (.arc ℓ)) : favoringStrategy p (.arc ℓ) s = 1 :=
  prod_bnode_arc ℓ _

theorem fav_cons (p ℓ : ℝ) (t : RTree) (s : SPure (.cons ℓ t)) :
    favoringStrategy p (.cons ℓ t) s = favoringStrategy p t (fun j => s (.down ℓ j)) := by
  unfold favoringStrategy; rw [prod_bnode_cons]; rfl

theorem fav_fork (p : ℝ) (t₁ t₂ : RTree) (s : SPure (.fork t₁ t₂)) :
    favoringStrategy p (.fork t₁ t₂) s = nodeLaw p t₁ t₂ (s (.root t₁ t₂)) *
      (favoringStrategy p t₁ (fun j => s (.left t₂ j)) *
        favoringStrategy p t₂ (fun j => s (.right t₁ j))) := by
  unfold favoringStrategy; rw [prod_bnode_fork]; rfl

theorem fav_glue (p : ℝ) (t₁ t₂ : RTree) (a : Action) (s₁ : SPure t₁) (s₂ : SPure t₂) :
    favoringStrategy p (.fork t₁ t₂) (glue a s₁ s₂) =
      nodeLaw p t₁ t₂ a * (favoringStrategy p t₁ s₁ * favoringStrategy p t₂ s₂) :=
  fav_fork p t₁ t₂ _

theorem bias_bounds {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) (t₁ t₂ : RTree)
    (a0 : 0 < t₁.length) (a3 : 0 ≤ meanDepth p t₁) (a4 : meanDepth p t₁ ≤ t₁.length)
    (b0 : 0 < t₂.length) (b3 : 0 ≤ meanDepth p t₂) (b4 : meanDepth p t₂ ≤ t₂.length) :
    0 ≤ bias p t₁ t₂ ∧ bias p t₁ t₂ ≤ 1 := by
  have hq : 0 ≤ 1 - p := by linarith
  unfold bias
  split_ifs with h
  · have hS : 0 < 2 * (p * t₁.length + (1 - p) * t₂.length) := by nlinarith
    refine ⟨div_nonneg (mul_nonneg (by linarith) (by linarith)) hS.le, ?_⟩
    rw [div_le_one hS]; nlinarith
  · have hS : 0 < 2 * (p * t₂.length + (1 - p) * t₁.length) := by nlinarith
    refine ⟨div_nonneg (mul_nonneg (by linarith) (by linarith)) hS.le, ?_⟩
    rw [div_le_one hS]; nlinarith

theorem nodeLaw_facts (p : ℝ) (t₁ t₂ : RTree) (h0 : 0 ≤ bias p t₁ t₂) (h1 : bias p t₁ t₂ ≤ 1) :
    (∀ a, 0 ≤ nodeLaw p t₁ t₂ a) ∧ ∑ a, nodeLaw p t₁ t₂ a = 1 := by
  refine ⟨fun a => ?_, ?_⟩
  · unfold nodeLaw; split_ifs <;> linarith
  · rw [sum_action]; unfold nodeLaw favored
    split_ifs <;> simp_all

theorem E_fav1 (p : ℝ) (t₁ t₂ : RTree) (h : meanDepth p t₂ ≤ meanDepth p t₁) :
    (∑ a, nodeLaw p t₁ t₂ a * (wrongFirst p a false * (2 * t₂.length)) =
      (1 - bias p t₁ t₂) * (1 - p) * (2 * t₂.length)) ∧
    (∑ a, nodeLaw p t₁ t₂ a * (wrongFirst p a true * (2 * t₁.length)) =
      (bias p t₁ t₂ + (1 - bias p t₁ t₂) * (1 - p)) * (2 * t₁.length)) := by
  constructor <;> rw [sum_action] <;> simp [nodeLaw, favored, h, wrongFirst] <;> ring

theorem E_fav2 (p : ℝ) (t₁ t₂ : RTree) (h : ¬ meanDepth p t₂ ≤ meanDepth p t₁) :
    (∑ a, nodeLaw p t₁ t₂ a * (wrongFirst p a false * (2 * t₂.length)) =
      (bias p t₁ t₂ + (1 - bias p t₁ t₂) * (1 - p)) * (2 * t₂.length)) ∧
    (∑ a, nodeLaw p t₁ t₂ a * (wrongFirst p a true * (2 * t₁.length)) =
      (1 - bias p t₁ t₂) * (1 - p) * (2 * t₁.length)) := by
  constructor <;> rw [sum_action] <;> simp [nodeLaw, favored, h, wrongFirst] <;> ring


theorem searcher_le {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) :
    ∀ t : RTree, t.PosLengths → (∀ s, 0 ≤ favoringStrategy p t s) ∧
      ∑ s, favoringStrategy p t s = 1 ∧
      ∀ v, ∑ s, favoringStrategy p t s * time p t s v ≤ Vt p t := by
  intro t
  induction t with
  | arc ℓ =>
    intro ht
    refine ⟨fun s => by rw [fav_arc]; norm_num, ?_, ?_⟩
    · rw [Fintype.sum_unique, fav_arc]
    · intro v; cases v
      rw [Fintype.sum_unique, fav_arc]
      show 1 * ℓ ≤ _
      unfold Vt; rw [meanDepth_arc]; simp only [RTree.length]; linarith
  | cons ℓ t ih =>
    intro ht
    simp only [RTree.PosLengths] at ht
    obtain ⟨i0, i1, i2⟩ := ih ht.2
    obtain ⟨-, -, h2, -, -⟩ := hider_facts hp hp1 t ht.2
    refine ⟨fun s => by rw [fav_cons]; exact i0 _, ?_, ?_⟩
    · rw [sum_spure_cons]; simp only [fav_cons]; exact i1
    · intro v; cases v with
      | down _ v =>
        rw [sum_spure_cons]
        have e : ∀ s : SPure t, favoringStrategy p (.cons ℓ t) (consGlue s) *
            time p (.cons ℓ t) (consGlue s) (.down ℓ v) =
            ℓ * favoringStrategy p t s + favoringStrategy p t s * time p t s v := by
          intro s; rw [fav_cons]
          show favoringStrategy p t s * (ℓ + time p t s v) = _; ring
        simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, i1]
        have := i2 v
        unfold Vt at this ⊢
        rw [meanDepth_cons_aux, h2]; simp only [RTree.length]; linarith
  | fork t₁ t₂ ih₁ ih₂ =>
    intro ht
    simp only [RTree.PosLengths] at ht
    obtain ⟨x0, x1, x2⟩ := ih₁ ht.1
    obtain ⟨y0, y1, y2⟩ := ih₂ ht.2
    obtain ⟨a0, -, -, a3, a4⟩ := hider_facts hp hp1 t₁ ht.1
    obtain ⟨b0, -, -, b3, b4⟩ := hider_facts hp hp1 t₂ ht.2
    obtain ⟨β0, β1⟩ := bias_bounds hp hp1 t₁ t₂ a0 a3 a4 b0 b3 b4
    obtain ⟨n0, n1⟩ := nodeLaw_facts p t₁ t₂ β0 β1
    have hq : 0 ≤ 1 - p := by linarith
    refine ⟨fun s => by
      rw [fav_fork]; exact mul_nonneg (n0 _) (mul_nonneg (x0 _) (y0 _)), ?_, ?_⟩
    · rw [sum_spure_fork]; simp only [fav_glue]
      rw [triple_one (nodeLaw p t₁ t₂) (favoringStrategy p t₁) (favoringStrategy p t₂)]
      rw [n1, x1, y1]; ring
    · intro v
      rw [sum_spure_fork]
      simp only [fav_glue]
      cases v with
      | left _ v =>
        have e : ∀ a s₁ s₂, time p (.fork t₁ t₂) (glue a s₁ s₂) (.left t₂ v) =
            wrongFirst p a false * (2 * t₂.length) + time p t₁ s₁ v := fun _ _ _ => rfl
        simp only [e]
        erw [triple_left (nodeLaw p t₁ t₂) (favoringStrategy p t₁) (favoringStrategy p t₂)
          (fun a => wrongFirst p a false * (2 * t₂.length)) (fun s₁ => time p t₁ s₁ v) x1 y1]
        rw [n1, one_mul, mul_one]
        have hx := x2 v
        suffices ∑ a, nodeLaw p t₁ t₂ a * (wrongFirst p a false * (2 * t₂.length)) + Vt p t₁ ≤
            Vt p (.fork t₁ t₂) by linarith
        unfold Vt; rw [meanDepth_fork]; simp only [RTree.length]
        by_cases h : meanDepth p t₂ ≤ meanDepth p t₁
        · rw [(E_fav1 p t₁ t₂ h).1]
          have hS : 0 < p * t₁.length + (1 - p) * t₂.length := by nlinarith
          simp only [bias, w1, w2, if_pos h]
          apply le_of_eq; field_simp; ring
        · rw [(E_fav2 p t₁ t₂ h).1]
          have hS : 0 < p * t₂.length + (1 - p) * t₁.length := by nlinarith
          simp only [bias, w1, w2, if_neg h]
          apply le_of_eq; field_simp; ring
      | right _ v =>
        have e : ∀ a s₁ s₂, time p (.fork t₁ t₂) (glue a s₁ s₂) (.right t₁ v) =
            wrongFirst p a true * (2 * t₁.length) + time p t₂ s₂ v := fun _ _ _ => rfl
        simp only [e]
        erw [triple_right (nodeLaw p t₁ t₂) (favoringStrategy p t₁) (favoringStrategy p t₂)
          (fun a => wrongFirst p a true * (2 * t₁.length)) (fun s₂ => time p t₂ s₂ v) x1 y1]
        rw [n1, one_mul, mul_one]
        have hy := y2 v
        suffices ∑ a, nodeLaw p t₁ t₂ a * (wrongFirst p a true * (2 * t₁.length)) + Vt p t₂ ≤
            Vt p (.fork t₁ t₂) by linarith
        unfold Vt; rw [meanDepth_fork]; simp only [RTree.length]
        by_cases h : meanDepth p t₂ ≤ meanDepth p t₁
        · rw [(E_fav1 p t₁ t₂ h).2]
          have hS : 0 < p * t₁.length + (1 - p) * t₂.length := by nlinarith
          simp only [bias, w1, w2, if_pos h]
          apply le_of_eq; field_simp; ring
        · rw [(E_fav2 p t₁ t₂ h).2]
          have hS : 0 < p * t₂.length + (1 - p) * t₁.length := by nlinarith
          simp only [bias, w1, w2, if_neg h]
          apply le_of_eq; field_simp; ring

end SignalSearch.Tree.T7Aux

namespace SignalSearch.Tree.T7Aux
open SignalSearch.Tree ZeroSumLP.DantzigExt

theorem main {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) (t : RTree) (ht : t.PosLengths) :
    IsMinMaxStrategy (payoff p t) (favoringStrategy p t) (Vt p t) ∧
      IsMaxMinStrategy (payoff p t) (hiderDist p t) (Vt p t) := by
  obtain ⟨x0, x1, x2⟩ := searcher_le hp hp1 t ht
  obtain ⟨-, y0, y1, -, -⟩ := hider_facts hp hp1 t ht
  have hy := hider_ge hp hp1 t ht
  exact assemble (payoff p t) (favoringStrategy p t) (hiderDist p t) (Vt p t)
    (fun s => x0 s) x1 (fun v => y0 v) y1
    (fun v => by
      calc ∑ j, payoff p t v j * favoringStrategy p t j
          = ∑ j, favoringStrategy p t j * time p t j v :=
            Finset.sum_congr rfl (fun j _ => mul_comm _ _)
        _ ≤ _ := x2 v)
    (fun s => hy s)

theorem value_unique_general {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ)
    (x : κ → ℝ) (V V' : ℝ) (hx : IsMinMaxStrategy A x V) (hV' : IsGameValue A V') : V' = V := by
  obtain ⟨x', hx'⟩ := hV'
  have h1 := hx.2 x' V' hx'.1
  have h2 := hx'.2 x V hx.1
  linarith

theorem isValue_iff {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) (t : RTree) (ht : t.PosLengths)
    (V : ℝ) : IsValue p t V ↔ V = Vt p t := by
  constructor
  · intro h; exact value_unique_general _ _ _ _ (main hp hp1 t ht).1 h
  · rintro rfl; exact ⟨_, (main hp hp1 t ht).1⟩

theorem Vt_cons (p ℓ : ℝ) (t : RTree) (h2 : ∑ v, hiderDist p t v = 1) :
    Vt p (.cons ℓ t) = ℓ + Vt p t := by
  unfold Vt; rw [meanDepth_cons_aux, h2]; simp only [RTree.length]; ring

end SignalSearch.Tree.T7Aux

open SignalSearch.Tree ZeroSumLP.DantzigExt SignalSearch.Tree.T7Aux

theorem solution (p : ℝ) (hp : 1 / 2 < p) (hp1 : p ≤ 1) (t : RTree) (ht : t.PosLengths) :
    (∃ V, IsValue p t V) ∧ ∀ V, IsValue p t V → V ≤ t.length := by
  refine ⟨⟨_, (isValue_iff hp hp1 t ht _).2 rfl⟩, fun V hV => ?_⟩
  rw [(isValue_iff hp hp1 t ht V).1 hV]
  obtain ⟨-, -, -, -, h4⟩ := hider_facts hp hp1 t ht
  unfold Vt; nlinarith
