-- Prove2me | solution 1 for Plasticity.C0Sum.not_hasPlasticUnitBall_of_ball_map
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-11-18T19:27:14.034624+00:00
-- url     : https://prove2.me/submissions/b295cb49-763f-4c1c-8823-608b34ae788e

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Order.Filter.Cofinite
import Mathlib.Topology.Algebra.Order.Group
import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_C0Sum

namespace Sol_Plasticity_C0Sum_not_hasPlasticUnitBall_of_ball_map

open Filter Topology Plasticity

section generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def mk (f : ℕ → E) (hf : Tendsto (fun i => ‖f i‖) cofinite (𝓝 0)) :
    c0Sum (fun _ : ℕ => E) :=
  ⟨⟨f, memℓp_infty (hf.bddAbove_range_of_cofinite)⟩, hf⟩

def val (a : c0Sum (fun _ : ℕ => E)) (n : ℕ) : E := (a : lp (fun _ : ℕ => E) ⊤) n

@[simp] lemma val_mk (f : ℕ → E) (hf) (n : ℕ) : val (mk f hf) n = f n := rfl

lemma val_ext {a b : c0Sum (fun _ : ℕ => E)} (h : ∀ n, val a n = val b n) : a = b := by
  apply Subtype.ext; apply lp.ext; funext n; exact h n

lemma tend (a : c0Sum (fun _ : ℕ => E)) : Tendsto (fun i => ‖val a i‖) cofinite (𝓝 0) := a.2

lemma val_sub (a b : c0Sum (fun _ : ℕ => E)) (n : ℕ) : val (a - b) n = val a n - val b n := rfl

lemma norm_val_le (a : c0Sum (fun _ : ℕ => E)) (n : ℕ) : ‖val a n‖ ≤ ‖a‖ :=
  lp.norm_apply_le_norm (by simp) (a : lp (fun _ : ℕ => E) ⊤) n

lemma norm_le_of (a : c0Sum (fun _ : ℕ => E)) {r : ℝ} (hr : 0 ≤ r) (h : ∀ n, ‖val a n‖ ≤ r) :
    ‖a‖ ≤ r := lp.norm_le_of_forall_le hr h

lemma tend_succ (a : c0Sum (fun _ : ℕ => E)) :
    Tendsto (fun i => ‖val a (i + 1)‖) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  have := tend a
  rw [Nat.cofinite_eq_atTop] at this
  exact (tendsto_add_atTop_iff_nat 1).2 this

lemma tend_cons (e : E) (g : ℕ → E) (hg : Tendsto (fun i => ‖g i‖) cofinite (𝓝 0)) :
    Tendsto (fun i => ‖(Nat.casesOn i e g : E)‖) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop] at *
  exact (tendsto_add_atTop_iff_nat 1).1 (by simpa using hg)

def shift (a : c0Sum (fun _ : ℕ => E)) : c0Sum (fun _ : ℕ => E) :=
  mk (fun n => val a (n + 1)) (tend_succ a)

def cons (e : E) (b : c0Sum (fun _ : ℕ => E)) : c0Sum (fun _ : ℕ => E) :=
  mk (fun i => (Nat.casesOn i e (val b) : E)) (tend_cons e _ (tend b))

@[simp] lemma val_shift (a : c0Sum (fun _ : ℕ => E)) (n) : val (shift a) n = val a (n+1) := rfl
@[simp] lemma val_cons_zero (e : E) (b : c0Sum (fun _ : ℕ => E)) : val (cons e b) 0 = e := rfl
@[simp] lemma val_cons_succ (e : E) (b : c0Sum (fun _ : ℕ => E)) (n) :
    val (cons e b) (n+1) = val b n := rfl

lemma shift_sub (a b : c0Sum (fun _ : ℕ => E)) : shift (a - b) = shift a - shift b :=
  val_ext fun n => by simp [val_sub]

lemma shift_cons_zero (e : E) : shift (cons e (0 : c0Sum (fun _ : ℕ => E))) = 0 :=
  val_ext fun n => rfl

lemma norm_cons_sub (a b : E) :
    ‖cons a (0 : c0Sum (fun _ : ℕ => E)) - cons b 0‖ = ‖a - b‖ := by
  apply le_antisymm
  · refine norm_le_of _ (norm_nonneg _) fun n => ?_
    cases n with
    | zero => exact le_rfl
    | succ n => show ‖(0:E) - 0‖ ≤ _; simp
  · exact norm_val_le (cons a (0 : c0Sum (fun _ : ℕ => E)) - cons b 0) 0
end generic

section main
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

lemma mem_ball_iff {E : Type*} [NormedAddCommGroup E] (x : E) : x ∈ Metric.closedBall (0:E) 1 ↔ ‖x‖ ≤ 1 := by
  simp

lemma norm_prod_le {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B] (z : A × B) :
    ‖z.1‖ ≤ ‖z‖ ∧ ‖z.2‖ ≤ ‖z‖ := ⟨le_max_left _ _, le_max_right _ _⟩

theorem main
    (F : Metric.closedBall (0 : X) 1 → Metric.closedBall (0 : Y) 1)
    (hF : LipschitzWith 1 F) (hbij : Function.Bijective F) (hiso : ¬ Isometry F) :
    ¬ HasPlasticUnitBall (c0Sum (fun _ : ℕ => X) × c0Sum (fun _ : ℕ => Y)) := by
  intro hP
  classical
  let e := Equiv.ofBijective F hbij
  let G : X → Y := fun x => if h : ‖x‖ ≤ 1 then (F ⟨x, (mem_ball_iff x).2 h⟩ : Y) else 0
  let H : Y → X := fun y => if h : ‖y‖ ≤ 1 then (e.symm ⟨y, (mem_ball_iff y).2 h⟩ : X) else 0
  have hG : ∀ u : Metric.closedBall (0:X) 1, G u = F u := fun u => by
    have h : ‖(u:X)‖ ≤ 1 := (mem_ball_iff _).1 u.2
    simp [G, h]
  have hH : ∀ v : Metric.closedBall (0:Y) 1, H v = e.symm v := fun v => by
    have h : ‖(v:Y)‖ ≤ 1 := (mem_ball_iff _).1 v.2
    simp [H, h]
  have hGn : ∀ x, ‖G x‖ ≤ 1 := fun x => by
    by_cases h : ‖x‖ ≤ 1
    · simp only [G, h, dif_pos]; exact (mem_ball_iff _).1 (F _).2
    · simp [G, h]
  have hHn : ∀ y, ‖H y‖ ≤ 1 := fun y => by
    by_cases h : ‖y‖ ≤ 1
    · simp only [H, h, dif_pos]; exact (mem_ball_iff _).1 (e.symm _).2
    · simp [H, h]
  have hGl : ∀ x x', ‖x‖ ≤ 1 → ‖x'‖ ≤ 1 → ‖G x - G x'‖ ≤ ‖x - x'‖ := fun x x' hx hx' => by
    have := hF.dist_le_mul ⟨x, (mem_ball_iff x).2 hx⟩ ⟨x', (mem_ball_iff x').2 hx'⟩
    rw [hG ⟨x, (mem_ball_iff x).2 hx⟩, hG ⟨x', (mem_ball_iff x').2 hx'⟩]
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm] at this
    simpa using this
  have hHG : ∀ x, ‖x‖ ≤ 1 → H (G x) = x := fun x hx => by
    have h1 := hG ⟨x, (mem_ball_iff x).2 hx⟩
    have h2 := hH (F ⟨x, (mem_ball_iff x).2 hx⟩)
    simp only at h1
    rw [h1, h2]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x, (mem_ball_iff x).2 hx⟩)
  have hGH : ∀ y, ‖y‖ ≤ 1 → G (H y) = y := fun y hy => by
    have h1 := hH ⟨y, (mem_ball_iff y).2 hy⟩
    simp only at h1
    rw [h1, hG]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, (mem_ball_iff y).2 hy⟩)
  let Z := c0Sum (fun _ : ℕ => X) × c0Sum (fun _ : ℕ => Y)
  let Tf : Z → Z := fun z => (shift z.1, cons (G (val z.1 0)) z.2)
  let Sf : Z → Z := fun w => (cons (H (val w.2 0)) w.1, shift w.2)
  have hT1 : ∀ z : Z, ‖z‖ ≤ 1 → ‖Tf z‖ ≤ 1 := fun z hz => by
    refine max_le (norm_le_of _ zero_le_one fun n => ?_) (norm_le_of _ zero_le_one fun n => ?_)
    · show ‖val z.1 (n+1)‖ ≤ 1
      exact (norm_val_le _ _).trans ((norm_prod_le z).1.trans hz)
    · cases n with
      | zero => exact hGn _
      | succ n =>
        show ‖val z.2 n‖ ≤ 1
        exact (norm_val_le _ _).trans ((norm_prod_le z).2.trans hz)
  have hS1 : ∀ z : Z, ‖z‖ ≤ 1 → ‖Sf z‖ ≤ 1 := fun z hz => by
    refine max_le (norm_le_of _ zero_le_one fun n => ?_) (norm_le_of _ zero_le_one fun n => ?_)
    · cases n with
      | zero => exact hHn _
      | succ n =>
        show ‖val z.1 n‖ ≤ 1
        exact (norm_val_le _ _).trans ((norm_prod_le z).1.trans hz)
    · show ‖val z.2 (n+1)‖ ≤ 1
      exact (norm_val_le _ _).trans ((norm_prod_le z).2.trans hz)
  have hTS : ∀ z : Z, ‖z‖ ≤ 1 → Tf (Sf z) = z := fun z hz => by
    have h0 : ‖val z.2 0‖ ≤ 1 := (norm_val_le _ _).trans ((norm_prod_le z).2.trans hz)
    refine Prod.ext (val_ext fun n => ?_) (val_ext fun n => ?_)
    · simp [Tf, Sf]
    · cases n with
      | zero => simp [Tf, Sf, hGH _ h0]
      | succ n => simp [Tf, Sf]
  have hST : ∀ z : Z, ‖z‖ ≤ 1 → Sf (Tf z) = z := fun z hz => by
    have h0 : ‖val z.1 0‖ ≤ 1 := (norm_val_le _ _).trans ((norm_prod_le z).1.trans hz)
    refine Prod.ext (val_ext fun n => ?_) (val_ext fun n => ?_)
    · cases n with
      | zero => simp [Tf, Sf, hHG _ h0]
      | succ n => simp [Tf, Sf]
    · simp [Tf, Sf]
  have hmem : ∀ z : Metric.closedBall (0:Z) 1, ‖(z:Z)‖ ≤ 1 := fun z => (mem_ball_iff _).1 z.2
  let T : Metric.closedBall (0:Z) 1 → Metric.closedBall (0:Z) 1 :=
    fun z => ⟨Tf z, (mem_ball_iff _).2 (hT1 z (hmem z))⟩
  have hlip : LipschitzWith 1 T := by
    refine LipschitzWith.of_dist_le_mul fun z z' => ?_
    simp only [NNReal.coe_one, one_mul]
    show dist (Tf z) (Tf z') ≤ dist (z:Z) z'
    rw [dist_eq_norm, dist_eq_norm, Prod.norm_def]
    have hz := hmem z
    have hz' := hmem z'
    have hd : ‖(z:Z) - z'‖ = max ‖(z:Z).1 - (z':Z).1‖ ‖(z:Z).2 - (z':Z).2‖ := rfl
    have h1 : ‖(z:Z).1 - (z':Z).1‖ ≤ ‖(z:Z) - z'‖ := le_max_left _ _
    have h2 : ‖(z:Z).2 - (z':Z).2‖ ≤ ‖(z:Z) - z'‖ := le_max_right _ _
    refine max_le (norm_le_of _ (norm_nonneg _) fun n => ?_) (norm_le_of _ (norm_nonneg _) fun n => ?_)
    · show ‖val (z:Z).1 (n+1) - val (z':Z).1 (n+1)‖ ≤ _
      rw [← val_sub]
      exact (norm_val_le _ _).trans h1
    · cases n with
      | zero =>
        show ‖G (val (z:Z).1 0) - G (val (z':Z).1 0)‖ ≤ _
        refine (hGl _ _ ?_ ?_).trans ?_
        · exact (norm_val_le _ _).trans ((norm_prod_le _).1.trans hz)
        · exact (norm_val_le _ _).trans ((norm_prod_le _).1.trans hz')
        · rw [← val_sub]; exact (norm_val_le _ _).trans h1
      | succ n =>
        show ‖val (z:Z).2 n - val (z':Z).2 n‖ ≤ _
        rw [← val_sub]
        exact (norm_val_le _ _).trans h2
  have hbijT : Function.Bijective T := by
    constructor
    · intro z z' h
      have := congrArg Subtype.val h
      have h' : Tf z = Tf z' := this
      apply Subtype.ext
      rw [← hST z (hmem z), ← hST z' (hmem z'), h']
    · intro w
      refine ⟨⟨Sf w, (mem_ball_iff _).2 (hS1 w (hmem w))⟩, Subtype.ext ?_⟩
      exact hTS w (hmem w)
  have hisoT := hP T hlip hbijT
  apply hiso
  refine Isometry.of_dist_eq fun u w => ?_
  have hc : ∀ x : Metric.closedBall (0:X) 1, ‖((cons (x:X) 0, 0) : Z)‖ ≤ 1 := fun x => by
    refine max_le (norm_le_of _ zero_le_one fun n => ?_) (by simp)
    cases n with
    | zero => exact (mem_ball_iff _).1 x.2
    | succ n => show ‖(0:X)‖ ≤ 1; simp
  have key := hisoT.dist_eq ⟨((cons (u:X) 0, 0) : Z), (mem_ball_iff _).2 (hc u)⟩
    ⟨((cons (w:X) 0, 0) : Z), (mem_ball_iff _).2 (hc w)⟩
  simp only [Subtype.dist_eq, Prod.dist_eq, dist_eq_norm, Prod.norm_def, T, Tf, Prod.fst_sub, Prod.snd_sub,
    sub_self, norm_zero, max_eq_left, norm_cons_sub, shift_cons_zero, val_cons_zero, hG] at key
  rw [Prod.dist_eq] at key
  simp only [dist_eq_norm, norm_cons_sub, sub_self, norm_zero, max_eq_left (norm_nonneg _)] at key
  have e1 : ‖(0 : c0Sum (fun _ : ℕ => X)) - 0‖ = 0 := by simp
  rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  simpa using key

end main
end Sol_Plasticity_C0Sum_not_hasPlasticUnitBall_of_ball_map

theorem solution {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : Metric.closedBall (0 : X) 1 → Metric.closedBall (0 : Y) 1)
    (hF : LipschitzWith 1 F) (hbij : Function.Bijective F) (hiso : ¬ Isometry F) :
    ¬ Plasticity.HasPlasticUnitBall (Plasticity.c0Sum (fun _ : ℕ => X) × Plasticity.c0Sum (fun _ : ℕ => Y)) :=
  Sol_Plasticity_C0Sum_not_hasPlasticUnitBall_of_ball_map.main F hF hbij hiso
