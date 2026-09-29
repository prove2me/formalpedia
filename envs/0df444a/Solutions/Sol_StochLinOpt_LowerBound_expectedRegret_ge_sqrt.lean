-- Prove2me | solution 1 for StochLinOpt.LowerBound.expectedRegret_ge_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:35:26.545888+00:00
-- url     : https://prove2.me/submissions/1416f0a3-f169-44bb-a3a2-7b710e4fb155

import Mathlib
import Definitions.Def_StochLinOpt_LowerBound_circleBandit

open MeasureTheory


namespace StochLinOpt.LowerBound

abbrev GPol := (t : ℕ) → (Fin t → Bool) → Fin 2 → ℝ

noncomputable def gm (θ : ℝ) (x : Fin 2 → ℝ) : ℝ := (Real.cos θ * x 0 + Real.sin θ * x 1) / 2
noncomputable def gm' (θ : ℝ) (x : Fin 2 → ℝ) : ℝ := (-Real.sin θ * x 0 + Real.cos θ * x 1) / 2

def gx (D : GPol) (T : ℕ) (ℓ : Fin T → Bool) (t : Fin T) : Fin 2 → ℝ :=
  D t (fun i => ℓ (Fin.castLE t.isLt.le i))

noncomputable def gq (θ : ℝ) (x : Fin 2 → ℝ) (σ : Bool) : ℝ := (1 + signVal σ * gm θ x) / 2

noncomputable def gf (D : GPol) (T : ℕ) (θ : ℝ) (ℓ : Fin T → Bool) : ℝ :=
  ∏ t : Fin T, gq θ (gx D T ℓ t) (ℓ t)

noncomputable def gs1 (θ : ℝ) (x : Fin 2 → ℝ) (σ : Bool) : ℝ :=
  signVal σ * gm' θ x / (1 + signVal σ * gm θ x)

noncomputable def gscore (D : GPol) (T : ℕ) (θ : ℝ) (ℓ : Fin T → Bool) : ℝ :=
  ∑ t : Fin T, gs1 θ (gx D T ℓ t) (ℓ t)

noncomputable def ga (θ : ℝ) (x : Fin 2 → ℝ) : ℝ := 1 + 2 * gm θ x

def gshift (D : GPol) (σ : Bool) : GPol := fun t h => D (t + 1) (Fin.cons σ h)

def GUnit (D : GPol) : Prop := ∀ t h, D t h 0 ^ 2 + D t h 1 ^ 2 = 1

lemma gshift_unit {D : GPol} (hD : GUnit D) (σ : Bool) : GUnit (gshift D σ) :=
  fun t h => hD (t+1) _

lemma sum_cons_split {β : Type*} [AddCommMonoid β] {n : ℕ} (F : (Fin (n+1) → Bool) → β) :
    ∑ ℓ, F ℓ = ∑ σ : Bool, ∑ ℓ' : Fin n → Bool, F (Fin.cons σ ℓ') := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type]; rfl

lemma gx_zero (D : GPol) (T : ℕ) (σ : Bool) (ℓ' : Fin T → Bool) :
    gx D (T+1) (Fin.cons σ ℓ') 0 = D 0 Fin.elim0 := by
  unfold gx; congr 1; funext i; exact i.elim0

lemma gx_succ (D : GPol) (T : ℕ) (σ : Bool) (ℓ' : Fin T → Bool) (t : Fin T) :
    gx D (T+1) (Fin.cons σ ℓ') t.succ = gx (gshift D σ) T ℓ' t := by
  unfold gx gshift
  simp only [Fin.val_succ]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [Fin.castLE]
    rfl

lemma gf_cons (D : GPol) (T : ℕ) (θ : ℝ) (σ : Bool) (ℓ' : Fin T → Bool) :
    gf D (T+1) θ (Fin.cons σ ℓ') = gq θ (D 0 Fin.elim0) σ * gf (gshift D σ) T θ ℓ' := by
  unfold gf
  rw [Fin.prod_univ_succ, gx_zero]
  simp only [Fin.cons_zero, Fin.cons_succ, gx_succ]

lemma gscore_cons (D : GPol) (T : ℕ) (θ : ℝ) (σ : Bool) (ℓ' : Fin T → Bool) :
    gscore D (T+1) θ (Fin.cons σ ℓ') = gs1 θ (D 0 Fin.elim0) σ + gscore (gshift D σ) T θ ℓ' := by
  unfold gscore
  rw [Fin.sum_univ_succ, gx_zero]
  simp only [Fin.cons_zero, Fin.cons_succ, gx_succ]

lemma gsumA_cons (D : GPol) (T : ℕ) (θ : ℝ) (σ : Bool) (ℓ' : Fin T → Bool) :
    ∑ t : Fin (T+1), ga θ (gx D (T+1) (Fin.cons σ ℓ') t)
      = ga θ (D 0 Fin.elim0) + ∑ t : Fin T, ga θ (gx (gshift D σ) T ℓ' t) := by
  rw [Fin.sum_univ_succ, gx_zero]
  simp only [gx_succ]

lemma gm_sq_add {θ : ℝ} {x : Fin 2 → ℝ} (hx : x 0 ^ 2 + x 1 ^ 2 = 1) :
    gm θ x ^ 2 + gm' θ x ^ 2 = 1 / 4 := by
  unfold gm gm'
  have := Real.sin_sq_add_cos_sq θ
  have e : (Real.cos θ * x 0 + Real.sin θ * x 1) ^ 2 + (-Real.sin θ * x 0 + Real.cos θ * x 1) ^ 2
      = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * (x 0 ^ 2 + x 1 ^ 2) := by ring
  have e2 : (Real.cos θ * x 0 + Real.sin θ * x 1) ^ 2 + (-Real.sin θ * x 0 + Real.cos θ * x 1) ^ 2
      = 1 := by rw [e, this, hx]; ring
  nlinarith

lemma gm_bound {θ : ℝ} {x : Fin 2 → ℝ} (hx : x 0 ^ 2 + x 1 ^ 2 = 1) :
    -1/2 ≤ gm θ x ∧ gm θ x ≤ 1/2 := by
  have := gm_sq_add (θ := θ) hx
  constructor <;> nlinarith [sq_nonneg (gm' θ x), sq_nonneg (gm θ x + 1/2), sq_nonneg (gm θ x - 1/2)]

lemma signVal_cases (σ : Bool) : signVal σ = 1 ∨ signVal σ = -1 := by
  cases σ <;> simp [signVal]

lemma gq_pos {θ : ℝ} {x : Fin 2 → ℝ} (hx : x 0 ^ 2 + x 1 ^ 2 = 1) (σ : Bool) :
    1/4 ≤ gq θ x σ := by
  have := gm_bound (θ := θ) hx
  unfold gq
  rcases signVal_cases σ with h | h <;> rw [h] <;> linarith

lemma gq_sum (θ : ℝ) (x : Fin 2 → ℝ) : ∑ σ : Bool, gq θ x σ = 1 := by
  simp [gq, signVal]; ring

lemma gf_pos (D : GPol) (hD : GUnit D) (T : ℕ) (θ : ℝ) (ℓ : Fin T → Bool) : 0 < gf D T θ ℓ := by
  unfold gf
  apply Finset.prod_pos
  intro t _
  have := gq_pos (θ := θ) (hD _ _) (ℓ t) (x := gx D T ℓ t)
  linarith

lemma gf_sum (T : ℕ) : ∀ (D : GPol) (θ : ℝ), ∑ ℓ, gf D T θ ℓ = 1 := by
  induction T with
  | zero => intro D θ; simp [gf]
  | succ T ih =>
    intro D θ
    rw [sum_cons_split]
    simp only [gf_cons, ← Finset.mul_sum, ih, mul_one]
    exact gq_sum _ _


lemma prod_hasDerivAt_gen : ∀ (n : ℕ) (g g' : Fin n → ℝ → ℝ) (θ : ℝ)
    (_ : ∀ t, HasDerivAt (g t) (g' t θ) θ) (_ : ∀ t, g t θ ≠ 0),
    HasDerivAt (fun θ => ∏ t, g t θ) ((∏ t, g t θ) * ∑ t, g' t θ / g t θ) θ := by
  intro n
  induction n with
  | zero => intro g g' θ _ _; simp; exact hasDerivAt_const _ _
  | succ n ih =>
    intro g g' θ hg hne
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ]
    have h1 := ih (fun t => g t.succ) (fun t => g' t.succ) θ (fun t => hg t.succ) (fun t => hne t.succ)
    have h2 := (hg 0).mul h1
    refine h2.congr_deriv ?_
    have := hne 0
    field_simp

lemma gm_hasDerivAt (θ : ℝ) (x : Fin 2 → ℝ) : HasDerivAt (fun θ => gm θ x) (gm' θ x) θ := by
  unfold gm gm'
  have h := (((Real.hasDerivAt_cos θ).mul_const (x 0)).add
    ((Real.hasDerivAt_sin θ).mul_const (x 1))).div_const 2
  exact h.congr_deriv (by ring)

lemma gm'_hasDerivAt (θ : ℝ) (x : Fin 2 → ℝ) :
    HasDerivAt (fun θ => gm' θ x) (-gm θ x) θ := by
  unfold gm gm'
  have h := ((((Real.hasDerivAt_sin θ).neg).mul_const (x 0)).add
    ((Real.hasDerivAt_cos θ).mul_const (x 1))).div_const 2
  refine h.congr_deriv (by ring)

lemma gf_hasDerivAt (D : GPol) (hD : GUnit D) (T : ℕ) (θ : ℝ) (ℓ : Fin T → Bool) :
    HasDerivAt (fun θ => gf D T θ ℓ) (gf D T θ ℓ * gscore D T θ ℓ) θ := by
  unfold gf gscore
  have := prod_hasDerivAt_gen T (fun t θ => gq θ (gx D T ℓ t) (ℓ t))
    (fun t θ => signVal (ℓ t) * gm' θ (gx D T ℓ t) / 2) θ
    (fun t => by
      unfold gq
      exact ((((gm_hasDerivAt θ _).const_mul (signVal (ℓ t))).const_add 1).div_const 2))
    (fun t => by have := gq_pos (θ := θ) (hD _ _) (ℓ t) (x := gx D T ℓ t); linarith)
  refine this.congr_deriv ?_
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  unfold gs1 gq
  have := gq_pos (θ := θ) (hD _ _) (ℓ t) (x := gx D T ℓ t)
  unfold gq at this
  have hne : 1 + signVal (ℓ t) * gm θ (gx D T ℓ t) ≠ 0 := by intro h; rw [h] at this; linarith
  field_simp

lemma gscore_mean (D : GPol) (hD : GUnit D) (T : ℕ) (θ : ℝ) :
    ∑ ℓ, gf D T θ ℓ * gscore D T θ ℓ = 0 := by
  have h1 : HasDerivAt (fun θ => ∑ ℓ, gf D T θ ℓ) (∑ ℓ, gf D T θ ℓ * gscore D T θ ℓ) θ :=
    HasDerivAt.fun_sum (fun ℓ _ => gf_hasDerivAt D hD T θ ℓ)
  have h2 : HasDerivAt (fun θ => ∑ ℓ, gf D T θ ℓ) 0 θ := by
    simp only [gf_sum]; exact hasDerivAt_const _ _
  exact h1.unique h2

lemma gs1_local {θ : ℝ} {x : Fin 2 → ℝ} (hx : x 0 ^ 2 + x 1 ^ 2 = 1) :
    ∑ σ : Bool, gq θ x σ * gs1 θ x σ ^ 2 ≤ 2/3 * ga θ x := by
  have hb := gm_bound (θ := θ) hx
  have hs := gm_sq_add (θ := θ) hx
  have hp : 0 < 1 + gm θ x := by linarith
  have hn : 0 < 1 - gm θ x := by linarith
  have e1 : ∀ σ : Bool, gq θ x σ * gs1 θ x σ ^ 2 = gm' θ x ^ 2 / (2 * (1 + signVal σ * gm θ x)) := by
    intro σ
    unfold gq gs1
    rcases signVal_cases σ with h | h <;> rw [h]
    · field_simp
    · have : (1 + -1 * gm θ x) ≠ 0 := by linarith
      field_simp
      try ring
  have e : ∑ σ : Bool, gq θ x σ * gs1 θ x σ ^ 2
      = gm' θ x ^ 2 / (2 * (1 + gm θ x)) + gm' θ x ^ 2 / (2 * (1 - gm θ x)) := by
    rw [Fintype.sum_bool, e1, e1]
    simp [signVal]; ring
  rw [e, div_add_div _ _ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
  unfold ga
  nlinarith [mul_nonneg hp.le hn.le, mul_nonneg (by linarith : (0:ℝ) ≤ gm θ x + 1/2)
    (by linarith : (0:ℝ) ≤ 1/2 - gm θ x), mul_nonneg (mul_nonneg hp.le hn.le)
    (by linarith : (0:ℝ) ≤ gm θ x + 1/2)]

lemma gfisher (T : ℕ) : ∀ (D : GPol) (_ : GUnit D) (θ : ℝ),
    ∑ ℓ, gf D T θ ℓ * gscore D T θ ℓ ^ 2
      ≤ ∑ ℓ, gf D T θ ℓ * (2/3 * ∑ t : Fin T, ga θ (gx D T ℓ t)) := by
  induction T with
  | zero => intro D _ θ; simp [gscore]
  | succ T ih =>
    intro D hD θ
    rw [sum_cons_split, sum_cons_split]
    simp only [gf_cons, gscore_cons, gsumA_cons]
    have hloc := gs1_local (θ := θ) (hD 0 Fin.elim0)
    set x0 := D 0 Fin.elim0
    have key : ∀ σ : Bool,
        ∑ ℓ' : Fin T → Bool, gq θ x0 σ * gf (gshift D σ) T θ ℓ' *
          (gs1 θ x0 σ + gscore (gshift D σ) T θ ℓ') ^ 2
        ≤ gq θ x0 σ * gs1 θ x0 σ ^ 2 +
          ∑ ℓ' : Fin T → Bool, gq θ x0 σ * gf (gshift D σ) T θ ℓ' *
            (2 / 3 * (ga θ x0 + ∑ t : Fin T, ga θ (gx (gshift D σ) T ℓ' t)))
          - gq θ x0 σ * (2/3 * ga θ x0) := by
      intro σ
      have hq : 0 ≤ gq θ x0 σ := by have := gq_pos (θ := θ) (hD 0 Fin.elim0) σ; linarith
      have hsum := gf_sum T (gshift D σ) θ
      have hmean := gscore_mean (gshift D σ) (gshift_unit hD σ) T θ
      have hih := ih (gshift D σ) (gshift_unit hD σ) θ
      have e1 : ∑ ℓ' : Fin T → Bool, gq θ x0 σ * gf (gshift D σ) T θ ℓ' *
          (gs1 θ x0 σ + gscore (gshift D σ) T θ ℓ') ^ 2
          = gq θ x0 σ * (gs1 θ x0 σ ^ 2 * ∑ ℓ', gf (gshift D σ) T θ ℓ'
            + 2 * gs1 θ x0 σ * ∑ ℓ', gf (gshift D σ) T θ ℓ' * gscore (gshift D σ) T θ ℓ'
            + ∑ ℓ', gf (gshift D σ) T θ ℓ' * gscore (gshift D σ) T θ ℓ' ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          Finset.mul_sum]
        apply Finset.sum_congr rfl; intro ℓ' _; ring
      have e2 : ∑ ℓ' : Fin T → Bool, gq θ x0 σ * gf (gshift D σ) T θ ℓ' *
            (2 / 3 * (ga θ x0 + ∑ t : Fin T, ga θ (gx (gshift D σ) T ℓ' t)))
          = gq θ x0 σ * (2/3 * ga θ x0 * ∑ ℓ', gf (gshift D σ) T θ ℓ'
            + ∑ ℓ', gf (gshift D σ) T θ ℓ' * (2/3 * ∑ t : Fin T, ga θ (gx (gshift D σ) T ℓ' t))) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro ℓ' _; ring
      rw [e1, e2, hsum, hmean]
      have := mul_le_mul_of_nonneg_left hih hq
      set F := ∑ ℓ', gf (gshift D σ) T θ ℓ' * gscore (gshift D σ) T θ ℓ' ^ 2
      set G := ∑ ℓ', gf (gshift D σ) T θ ℓ' * (2/3 * ∑ t : Fin T, ga θ (gx (gshift D σ) T ℓ' t))
      have h3 : gq θ x0 σ * (gs1 θ x0 σ ^ 2 * 1 + 2 * gs1 θ x0 σ * 0 + F)
          = gq θ x0 σ * gs1 θ x0 σ ^ 2 + gq θ x0 σ * F := by ring
      have h4 : gq θ x0 σ * gs1 θ x0 σ ^ 2 +
          gq θ x0 σ * (2/3 * ga θ x0 * 1 + G) - gq θ x0 σ * (2/3 * ga θ x0)
          = gq θ x0 σ * gs1 θ x0 σ ^ 2 + gq θ x0 σ * G := by ring
      rw [h3, h4]
      linarith
    calc _ ≤ ∑ σ : Bool, (gq θ x0 σ * gs1 θ x0 σ ^ 2 +
          ∑ ℓ' : Fin T → Bool, gq θ x0 σ * gf (gshift D σ) T θ ℓ' *
            (2 / 3 * (ga θ x0 + ∑ t : Fin T, ga θ (gx (gshift D σ) T ℓ' t)))
          - gq θ x0 σ * (2/3 * ga θ x0)) := Finset.sum_le_sum (fun σ _ => key σ)
      _ ≤ _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        simp only [← Finset.sum_mul, gq_sum]
        linarith


noncomputable def gb (θ : ℝ) (x : Fin 2 → ℝ) : ℝ := 2 * gm' θ x

lemma gm_cont (x : Fin 2 → ℝ) : Continuous (fun θ => gm θ x) :=
  continuous_iff_continuousAt.2 fun θ => (gm_hasDerivAt θ x).continuousAt
lemma gm'_cont (x : Fin 2 → ℝ) : Continuous (fun θ => gm' θ x) :=
  continuous_iff_continuousAt.2 fun θ => (gm'_hasDerivAt θ x).continuousAt
lemma gf_cont (D : GPol) (hD : GUnit D) (T : ℕ) (ℓ : Fin T → Bool) :
    Continuous (fun θ => gf D T θ ℓ) :=
  continuous_iff_continuousAt.2 fun θ => (gf_hasDerivAt D hD T θ ℓ).continuousAt
lemma gscore_cont (D : GPol) (hD : GUnit D) (T : ℕ) (ℓ : Fin T → Bool) :
    Continuous (fun θ => gscore D T θ ℓ) := by
  unfold gscore
  apply continuous_finset_sum
  intro t _
  unfold gs1
  apply Continuous.div
  · exact continuous_const.mul (gm'_cont _)
  · exact continuous_const.add (continuous_const.mul (gm_cont _))
  · intro θ
    have := gq_pos (θ := θ) (hD _ _) (ℓ t) (x := gx D T ℓ t)
    unfold gq at this; linarith

lemma gb_sq_le {θ : ℝ} {x : Fin 2 → ℝ} (hx : x 0 ^ 2 + x 1 ^ 2 = 1) :
    gb θ x ^ 2 ≤ 2 * ga θ x := by
  have hs := gm_sq_add (θ := θ) hx
  have hb := gm_bound (θ := θ) hx
  unfold gb ga
  nlinarith

lemma ga_nonneg {θ : ℝ} {x : Fin 2 → ℝ} (hx : x 0 ^ 2 + x 1 ^ 2 = 1) : 0 ≤ ga θ x := by
  have hb := gm_bound (θ := θ) hx
  unfold ga; linarith

/-- derivative of `G_t` -/
noncomputable def gP (D : GPol) (T : ℕ) (t : Fin T) (θ : ℝ) : ℝ :=
  ∑ ℓ, (gf D T θ ℓ * gscore D T θ ℓ * gb θ (gx D T ℓ t) + gf D T θ ℓ * (1 - ga θ (gx D T ℓ t)))

lemma gG_hasDerivAt (D : GPol) (hD : GUnit D) (T : ℕ) (t : Fin T) (θ : ℝ) :
    HasDerivAt (fun θ => ∑ ℓ, gf D T θ ℓ * gb θ (gx D T ℓ t)) (gP D T t θ) θ := by
  unfold gP
  apply HasDerivAt.fun_sum
  intro ℓ _
  have h1 := gf_hasDerivAt D hD T θ ℓ
  have h2 : HasDerivAt (fun θ => gb θ (gx D T ℓ t)) (1 - ga θ (gx D T ℓ t)) θ := by
    unfold gb ga
    exact ((gm'_hasDerivAt θ _).const_mul 2).congr_deriv (by ring)
  exact (h1.mul h2).congr_deriv (by ring)

lemma gP_cont (D : GPol) (hD : GUnit D) (T : ℕ) (t : Fin T) : Continuous (gP D T t) := by
  unfold gP
  apply continuous_finset_sum
  intro ℓ _
  have hb : Continuous (fun θ => gb θ (gx D T ℓ t)) := continuous_const.mul (gm'_cont _)
  have ha : Continuous (fun θ => ga θ (gx D T ℓ t)) :=
    continuous_const.add (continuous_const.mul (gm_cont _))
  exact (((gf_cont D hD T ℓ).mul (gscore_cont D hD T ℓ)).mul hb).add
    ((gf_cont D hD T ℓ).mul (continuous_const.sub ha))

noncomputable def gR (D : GPol) (T : ℕ) (θ : ℝ) : ℝ :=
  ∑ ℓ, gf D T θ ℓ * ∑ t : Fin T, ga θ (gx D T ℓ t)

lemma gR_cont (D : GPol) (hD : GUnit D) (T : ℕ) : Continuous (gR D T) := by
  unfold gR
  apply continuous_finset_sum
  intro ℓ _
  refine (gf_cont D hD T ℓ).mul (continuous_finset_sum _ fun t _ => ?_)
  exact continuous_const.add (continuous_const.mul (gm_cont _))

lemma gpointwise (D : GPol) (hD : GUnit D) (T : ℕ) (θ : ℝ) (lam : ℝ) (hlam : 0 < lam) :
    (T : ℝ) ≤ ∑ t : Fin T, gP D T t θ + (1 + lam * T / 3 + 1 / lam) * gR D T θ := by
  have hfis := gfisher T D hD θ
  have hsum := gf_sum T D θ
  -- per t
  have hper : ∀ t : Fin T, 1 ≤ gP D T t θ
      + lam / 2 * ∑ ℓ, gf D T θ ℓ * (2/3 * ∑ t : Fin T, ga θ (gx D T ℓ t))
      + (1 + 1 / lam) * ∑ ℓ, gf D T θ ℓ * ga θ (gx D T ℓ t) := by
    intro t
    have hpt : ∀ ℓ, gf D T θ ℓ * 1 ≤
        (gf D T θ ℓ * gscore D T θ ℓ * gb θ (gx D T ℓ t) + gf D T θ ℓ * (1 - ga θ (gx D T ℓ t)))
        + lam / 2 * (gf D T θ ℓ * gscore D T θ ℓ ^ 2)
        + (1 + 1 / lam) * (gf D T θ ℓ * ga θ (gx D T ℓ t)) := by
      intro ℓ
      have hf := (gf_pos D hD T θ ℓ).le
      have hb2 := gb_sq_le (θ := θ) (hD _ _) (x := gx D T ℓ t)
      set s := gscore D T θ ℓ
      set b := gb θ (gx D T ℓ t)
      set a := ga θ (gx D T ℓ t)
      set f := gf D T θ ℓ
      -- -s b ≤ lam/2 s^2 + b^2/(2 lam) ≤ lam/2 s^2 + a/lam
      have amgm : -(s * b) ≤ lam / 2 * s ^ 2 + 1 / lam * a := by
        have h1 : 0 ≤ (lam * s + b) ^ 2 := sq_nonneg _
        have h2 : -(s * b) ≤ lam / 2 * s ^ 2 + b ^ 2 / (2 * lam) := by
          rw [show lam / 2 * s ^ 2 + b ^ 2 / (2 * lam) = ((lam * s + b) ^ 2 - 2 * lam * s * b) / (2 * lam) by
            field_simp; ring]
          rw [le_div_iff₀ (by positivity)]; nlinarith
        have h3 : b ^ 2 / (2 * lam) ≤ 1 / lam * a := by
          rw [div_le_iff₀ (by positivity)]
          have : 1 / lam * a * (2 * lam) = 2 * a := by field_simp
          linarith
        linarith
      have := mul_le_mul_of_nonneg_left amgm hf
      nlinarith
    have := Finset.sum_le_sum (fun ℓ (_ : ℓ ∈ Finset.univ) => hpt ℓ)
    rw [← Finset.sum_mul, hsum, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum] at this
    unfold gP
    have h2 := mul_le_mul_of_nonneg_left hfis (by positivity : (0:ℝ) ≤ lam / 2)
    linarith
  have htot := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hper t)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at htot
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at htot
  have eR : ∑ t : Fin T, ∑ ℓ, gf D T θ ℓ * ga θ (gx D T ℓ t) = gR D T θ := by
    unfold gR; rw [Finset.sum_comm]; simp [Finset.mul_sum]
  have eR2 : ∑ ℓ, gf D T θ ℓ * (2/3 * ∑ t : Fin T, ga θ (gx D T ℓ t)) = 2/3 * gR D T θ := by
    unfold gR; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro ℓ _; ring
  have eR' : ∑ t : Fin T, (1 + 1 / lam) * ∑ ℓ, gf D T θ ℓ * ga θ (gx D T ℓ t)
      = (1 + 1 / lam) * gR D T θ := by rw [← Finset.mul_sum, eR]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htot
  rw [eR', eR2] at htot
  linarith


lemma gintegral (D : GPol) (hD : GUnit D) (T : ℕ) (hT : 1 ≤ T) :
    4 * Real.pi / 5 * Real.sqrt T ≤ ∫ θ in (0:ℝ)..(2 * Real.pi), gR D T θ := by
  have hT' : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hsq : 1 ≤ Real.sqrt T := by rw [Real.one_le_sqrt]; exact hT'
  have hsq2 : Real.sqrt T ^ 2 = T := Real.sq_sqrt (by linarith)
  have hpi := Real.pi_pos
  set r := Real.sqrt T with hr
  set lam := 1 / r with hlam
  have hlam0 : 0 < lam := by positivity
  set c' := 1 + lam * T / 3 + 1 / lam with hc'
  have hc'e : c' = 1 + r / 3 + r := by
    rw [hc', hlam, ← hsq2]; field_simp
  have hpt := fun θ => gpointwise D hD T θ lam hlam0
  have hint : ∀ t : Fin T, IntervalIntegrable (gP D T t) volume 0 (2 * Real.pi) :=
    fun t => (gP_cont D hD T t).intervalIntegrable _ _
  have hRint : IntervalIntegrable (gR D T) volume 0 (2 * Real.pi) :=
    (gR_cont D hD T).intervalIntegrable _ _
  have hsumint : IntervalIntegrable (fun θ => ∑ t : Fin T, gP D T t θ) volume 0 (2 * Real.pi) := by
    have := IntervalIntegrable.sum Finset.univ (fun t _ => hint t)
    refine this.congr (fun x _ => ?_)
    simp [Finset.sum_apply]
  have hmono : ∫ _θ in (0:ℝ)..(2 * Real.pi), (T : ℝ)
      ≤ ∫ θ in (0:ℝ)..(2 * Real.pi), (∑ t : Fin T, gP D T t θ + c' * gR D T θ) := by
    apply intervalIntegral.integral_mono_on (by positivity) intervalIntegrable_const
    · exact hsumint.add (hRint.const_mul c')
    · intro θ _; exact hpt θ
  have hP0 : ∀ t : Fin T, ∫ θ in (0:ℝ)..(2 * Real.pi), gP D T t θ = 0 := by
    intro t
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => gG_hasDerivAt D hD T t θ) (hint t)]
    simp [gf, gq, gb, gm, gm']
  rw [intervalIntegral.integral_add hsumint (hRint.const_mul c'),
    intervalIntegral.integral_finsetSum (fun t _ => hint t), intervalIntegral.integral_const_mul] at hmono
  simp only [hP0, Finset.sum_const_zero, zero_add, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul] at hmono
  rw [hc'e] at hmono
  set I := ∫ θ in (0:ℝ)..(2 * Real.pi), gR D T θ
  have hI : 0 ≤ I := by
    by_contra h
    push_neg at h
    have : (1 + r/3 + r) * I < 0 := mul_neg_of_pos_of_neg (by positivity) h
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hsq hI]


lemma meanVec_dot (θ : ℝ) (x : Fin 2 → ℝ) : meanVec θ ⬝ᵥ x = gm θ x := by
  simp [dotProduct, Fin.sum_univ_two, meanVec, gm]; ring

lemma unit_of_mem {x : Fin 2 → ℝ} (hx : x ∈ unitCircle) : x 0 ^ 2 + x 1 ^ 2 = 1 := by
  have : x ⬝ᵥ x = 1 := hx
  simp [dotProduct, Fin.sum_univ_two] at this; nlinarith

lemma optCost_meanVec (θ : ℝ) : optCost (meanVec θ) = -1/2 := by
  unfold optCost
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨![-Real.cos θ, -Real.sin θ], ?_, ?_⟩
    · show _ ⬝ᵥ _ = 1
      simp [dotProduct, Fin.sum_univ_two]; nlinarith [Real.sin_sq_add_cos_sq θ]
    · simp only
      rw [meanVec_dot]; simp [gm]; nlinarith [Real.sin_sq_add_cos_sq θ]
  · rintro y ⟨x, hx, rfl⟩
    simp only
    rw [meanVec_dot]
    exact (gm_bound (θ := θ) (unit_of_mem hx)).1

lemma condExpectedRegret_eq {S : Type} [MeasurableSpace S] (π : RandomizedPolicy S) (T : ℕ) (s : S)
    (θ : ℝ) : condExpectedRegret π T s (meanVec θ) = gR (fun t h => π.play t s h) T θ / 2 := by
  unfold condExpectedRegret gR
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ℓ _
  have e1 : costStringProb π T s (meanVec θ) ℓ = gf (fun t h => π.play t s h) T θ ℓ := by
    unfold costStringProb gf gq
    apply Finset.prod_congr rfl
    intro t _
    rw [meanVec_dot]; rfl
  have e2 : cumulativeRegret π T s (meanVec θ) ℓ
      = (∑ t : Fin T, ga θ (gx (fun t h => π.play t s h) T ℓ t)) / 2 := by
    unfold cumulativeRegret
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t _
    rw [meanVec_dot, optCost_meanVec]
    unfold ga; simp only [RandomizedPolicy.decisionAt, gx]; ring
  rw [e1, e2]; ring

lemma gR_bounds (D : GPol) (hD : GUnit D) (T : ℕ) (θ : ℝ) : 0 ≤ gR D T θ ∧ gR D T θ ≤ 2 * T := by
  unfold gR
  constructor
  · apply Finset.sum_nonneg; intro ℓ _
    exact mul_nonneg (gf_pos D hD T θ ℓ).le
      (Finset.sum_nonneg fun t _ => ga_nonneg (hD _ _))
  · calc ∑ ℓ, gf D T θ ℓ * ∑ t : Fin T, ga θ (gx D T ℓ t) ≤ ∑ ℓ, gf D T θ ℓ * (2 * T) := by
          apply Finset.sum_le_sum; intro ℓ _
          apply mul_le_mul_of_nonneg_left _ (gf_pos D hD T θ ℓ).le
          calc ∑ t : Fin T, ga θ (gx D T ℓ t) ≤ ∑ t : Fin T, (2:ℝ) := by
                apply Finset.sum_le_sum; intro t _
                have := gm_bound (θ := θ) (hD _ _) (x := gx D T ℓ t)
                unfold ga; linarith
            _ = 2 * T := by simp; ring
      _ = 2 * T := by rw [← Finset.sum_mul, gf_sum]; ring

lemma gR_meas {S : Type} [MeasurableSpace S] (π : RandomizedPolicy S) (T : ℕ) :
    Measurable (fun p : S × ℝ => gR (fun t h => π.play t p.1 h) T p.2) := by
  have hgm : ∀ (t : ℕ) (h : Fin t → Bool),
      Measurable (fun p : S × ℝ => gm p.2 (π.play t p.1 h)) := by
    intro t h
    have h0 : Measurable (fun p : S × ℝ => π.play t p.1 h 0) :=
      (measurable_pi_apply 0).comp ((π.measurable_play t h).comp measurable_fst)
    have h1 : Measurable (fun p : S × ℝ => π.play t p.1 h 1) :=
      (measurable_pi_apply 1).comp ((π.measurable_play t h).comp measurable_fst)
    unfold gm
    exact (((Real.measurable_cos.comp measurable_snd).mul h0).add
      ((Real.measurable_sin.comp measurable_snd).mul h1)).div_const 2
  unfold gR gf gq ga gx
  apply Finset.measurable_sum; intro ℓ _
  apply Measurable.mul
  · apply Finset.measurable_prod; intro t _
    exact ((measurable_const.mul (hgm _ _)).const_add 1).div_const 2
  · apply Finset.measurable_sum; intro t _
    exact (measurable_const.mul (hgm _ _)).const_add 1

theorem expectedRegret_core :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Type) [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]
        (π : RandomizedPolicy S) (T : ℕ), 1 ≤ T →
        c * Real.sqrt T ≤ expectedRegret ρ π T := by
  refine ⟨1/5, by norm_num, ?_⟩
  intro S _ ρ _ π T hT
  have hpi := Real.pi_pos
  have hD : ∀ s, GUnit (fun t h => π.play t s h) := fun s t h => unit_of_mem (π.play_mem t s h)
  have hinner : ∀ s, (2 * Real.pi)⁻¹ *
      (∫ θ in Set.Ico 0 (2 * Real.pi), condExpectedRegret π T s (meanVec θ))
      = (2 * Real.pi)⁻¹ * ((∫ θ in (0:ℝ)..(2 * Real.pi), gR (fun t h => π.play t s h) T θ) / 2) := by
    intro s
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
    simp only [condExpectedRegret_eq]
    rw [intervalIntegral.integral_div]
  unfold expectedRegret
  simp only [hinner]
  have hlow : ∀ s, 1/5 * Real.sqrt T ≤
      (2 * Real.pi)⁻¹ * ((∫ θ in (0:ℝ)..(2 * Real.pi), gR (fun t h => π.play t s h) T θ) / 2) := by
    intro s
    have := gintegral _ (hD s) T hT
    rw [← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    nlinarith
  have hmeas : StronglyMeasurable (fun s => (2 * Real.pi)⁻¹ *
      ((∫ θ in (0:ℝ)..(2 * Real.pi), gR (fun t h => π.play t s h) T θ) / 2)) := by
    have h1 : StronglyMeasurable (fun s => ∫ θ in Set.Ioc 0 (2 * Real.pi),
        gR (fun t h => π.play t s h) T θ) :=
      StronglyMeasurable.integral_prod_right (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))
      (f := fun s θ => gR (fun t h => π.play t s h) T θ) (gR_meas π T).stronglyMeasurable
    have h2 := ((StronglyMeasurable.measurable h1).div_const 2).const_mul (2 * Real.pi)⁻¹
    apply Measurable.stronglyMeasurable
    have e : (fun s => (2 * Real.pi)⁻¹ *
        ((∫ θ in (0:ℝ)..(2 * Real.pi), gR (fun t h => π.play t s h) T θ) / 2))
        = (fun s => (2 * Real.pi)⁻¹ * ((∫ θ in Set.Ioc 0 (2 * Real.pi),
          gR (fun t h => π.play t s h) T θ) / 2)) := by
      funext s; rw [intervalIntegral.integral_of_le (by positivity)]
    rw [e]; exact h2
  have hbound : ∀ s, ‖(2 * Real.pi)⁻¹ *
      ((∫ θ in (0:ℝ)..(2 * Real.pi), gR (fun t h => π.play t s h) T θ) / 2)‖ ≤ T := by
    intro s
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
      (C := 2 * T) (f := fun θ => gR (fun t h => π.play t s h) T θ) (fun θ _ => by
        have := gR_bounds _ (hD s) T θ
        rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)
    rw [sub_zero, abs_of_pos (by positivity)] at this
    rw [norm_mul, norm_div, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)]
    rw [Real.norm_two]
    rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    nlinarith
  have hint : Integrable (fun s => (2 * Real.pi)⁻¹ *
      ((∫ θ in (0:ℝ)..(2 * Real.pi), gR (fun t h => π.play t s h) T θ) / 2)) ρ :=
    Integrable.of_bound hmeas.aestronglyMeasurable T (Filter.Eventually.of_forall hbound)
  calc 1/5 * Real.sqrt T = ∫ _s, 1/5 * Real.sqrt T ∂ρ := by simp
    _ ≤ _ := integral_mono (integrable_const _) hint hlow

end StochLinOpt.LowerBound

open StochLinOpt.LowerBound


theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Type) [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]
        (π : RandomizedPolicy S) (T : ℕ), 1 ≤ T →
        c * Real.sqrt T ≤ expectedRegret ρ π T := by
  exact expectedRegret_core
