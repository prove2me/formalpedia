-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.calculus_regularization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:35:25.427992+00:00
-- url     : https://prove2.me/submissions/40ef66a0-4b24-4f88-860d-2abe85bcfb6a

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P05
universe u v w
variable {k : Type*} [RCLike k]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

theorem g58b_reg_one (f : P05.Symbol X k) :
    times (plus (constant 1) (absolute f)) (regularizer f) = constant 1 := by
  apply Subtype.ext; funext x
  simp only [times, plus, constant, absolute, regularizer]
  have h : (1 : k) + ((‖f.val x‖ : ℝ) : k) = ((1 + ‖f.val x‖ : ℝ) : k) := by push_cast; ring
  rw [h]; exact mul_inv_cancel₀ (RCLike.ofReal_ne_zero.mpr (by positivity))

theorem g58b_reg_one' (f : P05.Symbol X k) :
    times (regularizer f) (plus (constant 1) (absolute f)) = constant 1 := by
  rw [show times (regularizer f) (plus (constant 1) (absolute f)) =
    times (plus (constant 1) (absolute f)) (regularizer f) from
    Subtype.ext (funext fun x => mul_comm _ _)]
  exact g58b_reg_one f

theorem g58b_reg_f (f : P05.Symbol X k) :
    times (plus (constant 1) (absolute f)) (times (regularizer f) f) = f := by
  have := congrArg (fun s : P05.Symbol X k => s.val) (g58b_reg_one f)
  apply Subtype.ext; funext x
  have hx := congrFun this x
  simp only [times, constant] at hx ⊢
  rw [← mul_assoc, hx, one_mul]

theorem g58b_reg_bdd (f : P05.Symbol X k) :
    BoundedSymbol (regularizer f) ∧ BoundedSymbol (times (regularizer f) f) := by
  refine ⟨⟨1, fun x => ?_⟩, ⟨1, fun x => ?_⟩⟩
  · simp only [regularizer, norm_inv, RCLike.norm_ofReal]
    rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith [norm_nonneg (f.val x)])
  · simp only [times, regularizer, norm_mul, norm_inv, RCLike.norm_ofReal]
    rw [abs_of_pos (by positivity), inv_mul_le_iff₀ (by positivity)]
    linarith [norm_nonneg (f.val x)]

theorem g58b_regularization (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k) :
    BoundedSymbol (regularizer f) ∧ BoundedSymbol (times (regularizer f) f) ∧
    BoundedOperator (k := k) (F (regularizer f)) ∧
    BoundedOperator (k := k) (F (times (regularizer f) f)) ∧
    InjectiveOperator (F (regularizer f)) ∧
    F f = mul (inverse (F (regularizer f))) (F (times (regularizer f) f)) ∧
    ∀ x y, (x, y) ∈ F f ↔
      ∃ z, (x, z) ∈ F (times (regularizer f) f) ∧ (y, z) ∈ F (regularizer f) := by
  obtain ⟨hcl, ⟨h1, hadd, hsc, hmul, hdom⟩, hbd, hw⟩ := hF
  obtain ⟨be, bef⟩ := g58b_reg_bdd f
  obtain ⟨⟨Te, hTe⟩, -⟩ := hbd _ be
  obtain ⟨⟨Tef, hTef⟩, -⟩ := hbd _ bef
  set g := plus (constant 1) (absolute f)
  -- (Te u, u) ∈ F g
  have step1 : ∀ u, (Te u, u) ∈ F g := by
    intro u
    have hu : u ∈ graphDomain (mul (F g) (F (regularizer f))) := by
      rw [hdom, hTe, g58b_reg_one, h1]
      exact ⟨⟨Te u, rfl⟩, ⟨u, rfl⟩⟩
    obtain ⟨w, z, hz, hzw⟩ := hu
    have hz' : z = Te u := by rw [hTe] at hz; exact hz
    have hw' : (u, w) ∈ F (times g (regularizer f)) := hmul _ _ ⟨z, hz, hzw⟩
    rw [g58b_reg_one, h1] at hw'
    have : w = u := hw'
    rw [hz', this] at hzw; exact hzw
  have hinj : InjectiveOperator (F (regularizer f)) := by
    intro x z y hx hz
    rw [hTe] at hx hz
    have e1 : y = Te x := hx
    have e2 : y = Te z := hz
    exact (hcl g).2.2.2.2.2 _ _ _ (step1 x) (e1 ▸ e2 ▸ step1 z)
  have key : ∀ x y, (x, y) ∈ F f ↔
      ∃ z, (x, z) ∈ F (times (regularizer f) f) ∧ (y, z) ∈ F (regularizer f) := by
    intro x y
    constructor
    · intro hxy
      refine ⟨Te y, hmul _ _ ⟨y, hxy, ?_⟩, ?_⟩
      · rw [hTe]; rfl
      · rw [hTe]; rfl
    · rintro ⟨z, hxz, hyz⟩
      have hz : z = Te y := by rw [hTe] at hyz; exact hyz
      have := hmul g (times (regularizer f) f)
        (show (x, y) ∈ mul _ _ from ⟨z, hxz, by rw [hz]; exact step1 y⟩)
      rwa [g58b_reg_f] at this
  refine ⟨be, bef, ⟨Te, hTe⟩, ⟨Tef, hTef⟩, hinj, ?_, key⟩
  ext ⟨x, y⟩
  rw [key]
  rfl

theorem solution (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k) :
    BoundedSymbol (regularizer f) ∧ BoundedSymbol (times (regularizer f) f) ∧
    BoundedOperator (k := k) (F (regularizer f)) ∧
    BoundedOperator (k := k) (F (times (regularizer f) f)) ∧
    InjectiveOperator (F (regularizer f)) ∧
    F f = mul (inverse (F (regularizer f))) (F (times (regularizer f) f)) ∧
    ∀ x y, (x, y) ∈ F f ↔
      ∃ z, (x, z) ∈ F (times (regularizer f) f) ∧ (y, z) ∈ F (regularizer f) :=
  g58b_regularization F hF f
