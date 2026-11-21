-- Prove2me | solution 1 for OptimalAgnosticPAC.Learner.eq_4_rademacher_width
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:02:56.67417+00:00
-- url     : https://prove2.me/submissions/ee5144af-1242-440a-b9ed-f960fcce4388

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Cube
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_OptimalAgnosticPAC_Learner_Risk

section
open scoped Classical

namespace OptimalAgnosticPAC.Dev.Eq4a
open OptimalAgnosticPAC.Learner

variable {P : Type} [Fintype P]

/-- average over the cube -/
noncomputable def avg (f : (P → Bool) → ℝ) : ℝ := (Fintype.card (P → Bool) : ℝ)⁻¹ * ∑ ε, f ε

theorem card_cube_pos : (0 : ℝ) < Fintype.card (P → Bool) := by
  exact_mod_cast Fintype.card_pos

theorem avg_mono {f g : (P → Bool) → ℝ} (h : ∀ ε, f ε ≤ g ε) : avg f ≤ avg g := by
  unfold avg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ε _ => h ε) (by have := card_cube_pos (P := P); positivity)

theorem avg_add (f g : (P → Bool) → ℝ) : avg (fun ε => f ε + g ε) = avg f + avg g := by
  unfold avg; rw [Finset.sum_add_distrib]; ring

theorem avg_sum {ι : Type} (s : Finset ι) (f : ι → (P → Bool) → ℝ) :
    avg (fun ε => ∑ i ∈ s, f i ε) = ∑ i ∈ s, avg (f i) := by
  unfold avg; rw [Finset.sum_comm, Finset.mul_sum]

theorem avg_mul_left (c : ℝ) (f : (P → Bool) → ℝ) : avg (fun ε => c * f ε) = c * avg f := by
  unfold avg; rw [← Finset.mul_sum]; ring

theorem avg_prod (h : P → Bool → ℝ) :
    avg (fun ε => ∏ p, h p (ε p)) = ∏ p, ((h p true + h p false) / 2) := by
  unfold avg
  have h1 : ∏ p, (∑ b : Bool, h p b) = ∑ ε : P → Bool, ∏ p, h p (ε p) := by
    have := Finset.prod_univ_sum (fun _ : P => (Finset.univ : Finset Bool)) (fun p b => h p b)
    rw [Fintype.piFinset_univ] at this
    exact this
  rw [← h1]
  simp only [Fintype.sum_bool]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  rw [Fintype.card_fun, Fintype.card_bool]
  push_cast
  rw [inv_mul_eq_div]

theorem avg_exp_lin (g : P → ℝ) (l : ℝ) :
    avg (fun ε => Real.exp (l * ∑ p, sgn (ε p) * g p)) ≤ Real.exp (l ^ 2 * (∑ p, g p ^ 2) / 2) := by
  have e1 : ∀ ε : P → Bool, Real.exp (l * ∑ p, sgn (ε p) * g p) =
      ∏ p, Real.exp (l * (sgn (ε p) * g p)) := by
    intro ε
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [e1]
  rw [avg_prod (fun p b => Real.exp (l * (sgn b * g p)))]
  have e2 : ∀ p, (Real.exp (l * (sgn true * g p)) + Real.exp (l * (sgn false * g p))) / 2 ≤
      Real.exp (l ^ 2 * g p ^ 2 / 2) := by
    intro p
    have := Real.cosh_le_exp_half_sq (l * g p)
    rw [Real.cosh_eq] at this
    simp only [sgn, if_true, Bool.false_eq_true, if_false]
    have a1 : l * (1 * g p) = l * g p := by ring
    have a2 : l * (-1 * g p) = -(l * g p) := by ring
    rw [a1, a2]
    calc _ = (Real.exp (l * g p) + Real.exp (-(l * g p))) / 2 := rfl
      _ ≤ Real.exp ((l * g p) ^ 2 / 2) := this
      _ = _ := by congr 1; ring
  calc ∏ p, ((Real.exp (l * (sgn true * g p)) + Real.exp (l * (sgn false * g p))) / 2)
      ≤ ∏ p, Real.exp (l ^ 2 * g p ^ 2 / 2) := by
        apply Finset.prod_le_prod
        · intro p _
          have := Real.exp_pos (l * (sgn true * g p)); have := Real.exp_pos (l * (sgn false * g p))
          positivity
        · intro p _; exact e2 p
    _ = Real.exp (l ^ 2 * (∑ p, g p ^ 2) / 2) := by
        rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_div]

theorem opt_lambda (A a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ l : ℝ, 0 < l → A ≤ a / l + l * b) : A ≤ 2 * Real.sqrt (a * b) := by
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · subst hb0
    simp only [mul_zero, add_zero] at h
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · subst ha0; simp at h ⊢; simpa using h 1 one_pos
    · simp only [mul_zero, Real.sqrt_zero]
      by_contra hlt
      have hA : 0 < A := by simpa using hlt
      have := h (2 * a / A) (by positivity)
      have e : a / (2 * a / A) = A / 2 := by field_simp
      linarith
  · rcases eq_or_lt_of_le ha with ha0 | hapos
    · subst ha0
      simp only [zero_mul, zero_div, zero_add, Real.sqrt_zero, mul_zero] at h ⊢
      by_contra hlt; push Not at hlt
      have := h (A / (2 * b)) (by positivity)
      have : A * (1 - 1/2) ≤ 0 := by field_simp at this ⊢; nlinarith
      nlinarith
    · have hs := Real.sqrt_pos.2 (mul_pos hapos hbpos)
      have hsq := Real.sq_sqrt (mul_pos hapos hbpos).le
      have := h (Real.sqrt (a * b) / b) (by positivity)
      have e : a / (Real.sqrt (a * b) / b) + Real.sqrt (a * b) / b * b = 2 * Real.sqrt (a * b) := by
        field_simp
        nlinarith
      linarith


theorem jensen_exp (M : (P → Bool) → ℝ) :
    Real.exp (avg M) ≤ avg (fun ε => Real.exp (M ε)) := by
  have hc := card_cube_pos (P := P)
  have := convexOn_exp.map_sum_le (t := (Finset.univ : Finset (P → Bool)))
    (w := fun _ => (Fintype.card (P → Bool) : ℝ)⁻¹) (p := M) (fun _ _ => by positivity)
    (by simp) (fun _ _ => Set.mem_univ _)
  simpa [avg, ← Finset.mul_sum] using this

theorem massart (G : Finset (P → ℝ)) (hG : G.Nonempty) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ g ∈ G, ∑ p, g p ^ 2 ≤ r ^ 2) :
    avg (fun ε => G.sup' hG (fun g => ∑ p, sgn (ε p) * g p)) ≤
      r * Real.sqrt (2 * Real.log G.card) := by
  set M : (P → Bool) → ℝ := fun ε => G.sup' hG (fun g => ∑ p, sgn (ε p) * g p) with hM
  have hcard : (1 : ℝ) ≤ G.card := by exact_mod_cast hG.card_pos
  have hcpos : (0 : ℝ) < G.card := by linarith
  have key : ∀ l : ℝ, 0 < l → avg M ≤ Real.log G.card / l + l * (r ^ 2 / 2) := by
    intro l hl
    have h1 : Real.exp (l * avg M) ≤ G.card * Real.exp (l ^ 2 * r ^ 2 / 2) := by
      have j := jensen_exp (fun ε => l * M ε)
      have e : avg (fun ε => l * M ε) = l * avg M := avg_mul_left _ _
      rw [e] at j
      refine j.trans ?_
      have h2 : ∀ ε, Real.exp (l * M ε) ≤ ∑ g ∈ G, Real.exp (l * ∑ p, sgn (ε p) * g p) := by
        intro ε
        obtain ⟨g0, hg0, he⟩ := Finset.exists_mem_eq_sup' hG (fun g => ∑ p, sgn (ε p) * g p)
        have : M ε = ∑ p, sgn (ε p) * g0 p := he
        rw [this]
        exact Finset.single_le_sum (f := fun g => Real.exp (l * ∑ p, sgn (ε p) * g p))
          (fun _ _ => (Real.exp_pos _).le) hg0
      refine (avg_mono h2).trans ?_
      rw [avg_sum]
      calc ∑ g ∈ G, avg (fun ε => Real.exp (l * ∑ p, sgn (ε p) * g p))
          ≤ ∑ g ∈ G, Real.exp (l ^ 2 * r ^ 2 / 2) := by
            apply Finset.sum_le_sum; intro g hg
            refine (avg_exp_lin g l).trans ?_
            apply Real.exp_le_exp.2
            have := h g hg
            have : l ^ 2 * (∑ p, g p ^ 2) ≤ l ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_left this (sq_nonneg _)
            linarith
        _ = _ := by simp
    have h3 : l * avg M ≤ Real.log G.card + l ^ 2 * r ^ 2 / 2 := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rw [Real.log_exp, Real.log_mul hcpos.ne' (Real.exp_pos _).ne', Real.log_exp] at this
      exact this
    have : avg M * l ≤ Real.log G.card + l * l * (r ^ 2 / 2) := by nlinarith
    rw [div_add' _ _ _ hl.ne', le_div_iff₀ hl]
    nlinarith
  have := opt_lambda (avg M) (Real.log G.card) (r ^ 2 / 2) (Real.log_nonneg hcard)
    (by positivity) key
  refine this.trans (le_of_eq ?_)
  rw [show Real.log G.card * (r ^ 2 / 2) = (r / 2) ^ 2 * (2 * Real.log G.card) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  ring

end OptimalAgnosticPAC.Dev.Eq4a
end

section
open scoped Classical
namespace OptimalAgnosticPAC.Dev.T2b
open OptimalAgnosticPAC.Learner

theorem vc_trace_le {X : Type} (H : Set (X → Bool)) {n : ℕ} (x : Fin n → X) :
    HighDimProb.Chaining.vcDim (trace H x) ≤ HighDimProb.Chaining.vcDim H := by
  unfold HighDimProb.Chaining.vcDim
  refine iSup_le (fun ⟨Λ, hΛ⟩ => ?_)
  have hinj : Set.InjOn x Λ := by
    intro i hi j hj hij
    by_contra hne
    obtain ⟨f, ⟨h, hh, rfl⟩, hf⟩ := hΛ (fun k => decide (k.1 = i))
    have h1 : h (x i) = true := by simpa using hf ⟨i, hi⟩
    have hji : ¬ j = i := fun e => hne e.symm
    have h2 : h (x j) = false := by simpa [hji] using hf ⟨j, hj⟩
    rw [← hij, h1] at h2
    exact absurd h2 (by simp)
  have hsh : HighDimProb.Chaining.Shatters H (x '' Λ) := by
    intro g'
    obtain ⟨f, ⟨h, hh, rfl⟩, hf⟩ := hΛ (fun k => g' ⟨x k.1, Set.mem_image_of_mem x k.2⟩)
    refine ⟨h, hh, ?_⟩
    rintro ⟨y, k, hk, rfl⟩
    exact hf ⟨k, hk⟩
  calc Λ.encard = (x '' Λ).encard := (hinj.encard_image).symm
    _ ≤ _ := le_iSup (fun Λ' : {Λ : Set X // HighDimProb.Chaining.Shatters H Λ} => Λ'.1.encard)
        ⟨x '' Λ, hsh⟩

end OptimalAgnosticPAC.Dev.T2b
end

section
open scoped Classical

namespace OptimalAgnosticPAC.Dev.Eq4b
open OptimalAgnosticPAC.Learner

/-- Sauer-Shelah for the trace on a sequence. -/
theorem sauer_trace {X : Type} (H : Set (X → Bool)) (d m : ℕ)
    (hVC : HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞)) (x : Fin m → X) :
    (trace H x).ncard ≤ ∑ k ∈ Finset.range (d + 1), m.choose k := by
  have hfin : (trace H x).Finite := Set.toFinite _
  set T : Finset (Fin m → Bool) := hfin.toFinset with hT
  set 𝒜 : Finset (Finset (Fin m)) := T.image (fun g => Finset.univ.filter (fun i => g i = true)) with hA
  have hinj : Function.Injective (fun g : Fin m → Bool => Finset.univ.filter (fun i => g i = true)) := by
    intro g g' h
    funext i
    have := congrArg (fun s => i ∈ s) h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    cases hg : g i <;> cases hg' : g' i <;> simp_all
  have hcard : 𝒜.card = (trace H x).ncard := by
    rw [hA, Finset.card_image_of_injective _ hinj, ← Set.ncard_coe_finset, hT, Set.Finite.coe_toFinset]
  have hvc : 𝒜.vcDim ≤ d := by
    unfold Finset.vcDim
    refine Finset.sup_le fun s hs => ?_
    have hsh : 𝒜.Shatters s := (Finset.mem_shatterer).1 hs
    have hsh' : HighDimProb.Chaining.Shatters (trace H x) (↑s : Set (Fin m)) := by
      intro g
      obtain ⟨u, hu, hsu⟩ := hsh (t := s.filter (fun i => ∃ hi : i ∈ s, g ⟨i, hi⟩ = true)) (Finset.filter_subset _ _)
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hu
      refine ⟨f, by simpa [hT] using hf, ?_⟩
      rintro ⟨y, hy⟩
      have h1 := congrArg (fun S => y ∈ S) hsu
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at h1
      have h2 : f y = true ↔ g ⟨y, hy⟩ = true := by
        constructor
        · intro hfy
          obtain ⟨_, hi, hg⟩ := h1.1 ⟨hy, hfy⟩
          exact hg
        · intro hg
          exact (h1.2 ⟨hy, hy, hg⟩).2
      cases hf1 : f y <;> cases hg1 : g ⟨y, hy⟩ <;> simp_all
    have h3 : (s.card : ℕ∞) ≤ d := by
      calc (s.card : ℕ∞) = (↑s : Set (Fin m)).encard := (Set.encard_coe_eq_coe_finsetCard s).symm
        _ ≤ HighDimProb.Chaining.vcDim (trace H x) :=
            le_iSup (fun Λ' : {Λ : Set (Fin m) // HighDimProb.Chaining.Shatters (trace H x) Λ} => Λ'.1.encard) ⟨↑s, hsh'⟩
        _ ≤ HighDimProb.Chaining.vcDim H := OptimalAgnosticPAC.Dev.T2b.vc_trace_le H x
        _ ≤ d := hVC
    exact_mod_cast h3
  have h4 := Finset.card_le_card_shatterer 𝒜
  have h5 := Finset.card_shatterer_le_sum_vcDim (𝒜 := 𝒜)
  rw [← hcard]
  refine h4.trans (h5.trans ?_)
  simp only [Fintype.card_fin]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  simp only [Finset.mem_Iic] at hk
  simp only [Finset.mem_range]; omega

/-- `∑_{k ≤ d} C(m,k) ≤ (e m / d)^d` for `1 ≤ d ≤ m`. -/
theorem sum_choose_le (d m : ℕ) (hd : 1 ≤ d) (hdm : d ≤ m) :
    (∑ k ∈ Finset.range (d + 1), (m.choose k : ℝ)) ≤ (Real.exp 1 * m / d) ^ d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast (hd.trans hdm)
  have hle : (d : ℝ) ≤ m := by exact_mod_cast hdm
  set q : ℝ := d / m with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hmR]; exact hle
  -- step 1: sum * q^d ≤ (1+q)^m
  have h1 : (∑ k ∈ Finset.range (d + 1), (m.choose k : ℝ)) * q ^ d ≤ (q + 1) ^ m := by
    rw [add_pow, Finset.sum_mul]
    calc ∑ k ∈ Finset.range (d + 1), (m.choose k : ℝ) * q ^ d
        ≤ ∑ k ∈ Finset.range (d + 1), q ^ k * 1 ^ (m - k) * (m.choose k : ℝ) := by
          apply Finset.sum_le_sum; intro k hk
          have hk' : k ≤ d := by simpa [Nat.lt_succ_iff] using hk
          have : q ^ d ≤ q ^ k := pow_le_pow_of_le_one hq0.le hq1 hk'
          simp only [one_pow, mul_one]
          nlinarith [(Nat.cast_nonneg (m.choose k) : (0:ℝ) ≤ m.choose k)]
      _ ≤ ∑ k ∈ Finset.range (m + 1), q ^ k * 1 ^ (m - k) * (m.choose k : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
          · intros; positivity
  have h2 : (q + 1) ^ m ≤ Real.exp d := by
    calc (q + 1) ^ m ≤ (Real.exp q) ^ m := by
          apply pow_le_pow_left₀ (by positivity); linarith [Real.add_one_le_exp q]
      _ = Real.exp d := by rw [← Real.exp_nat_mul, hq]; congr 1; field_simp
  have h3 : (∑ k ∈ Finset.range (d + 1), (m.choose k : ℝ)) ≤ Real.exp d / q ^ d := by
    rw [le_div_iff₀ (by positivity)]; linarith
  refine h3.trans (le_of_eq ?_)
  have e : Real.exp d = Real.exp 1 ^ d := by rw [← Real.exp_nat_mul]; simp
  rw [e, hq, div_pow, div_pow, mul_pow]
  field_simp

end OptimalAgnosticPAC.Dev.Eq4b
end

section
open scoped Classical

namespace OptimalAgnosticPAC.Dev.Eq4c
open OptimalAgnosticPAC.Learner

variable {P : Type} [Fintype P]

/-- Hamming distance on the coordinates `D`. -/
noncomputable def dd (D : Finset P) (f g : P → Bool) : ℕ := (D.filter (fun p => f p ≠ g p)).card

theorem dd_symm (D : Finset P) (f g : P → Bool) : dd D f g = dd D g f := by
  unfold dd; congr 1; ext p; simp [ne_comm]

theorem dd_self (D : Finset P) (f : P → Bool) : dd D f f = 0 := by simp [dd]

theorem agree_card (D : Finset P) (f g : P → Bool) :
    (D.filter (fun p => f p = g p)).card + dd D f g = D.card := by
  unfold dd
  exact Finset.card_filter_add_card_filter_not (s := D) (fun p => f p = g p) |>.trans rfl

/-- number of sequences in `D^m` on which `f` and `g` agree everywhere -/
theorem count_agree (D : Finset P) (m : ℕ) (f g : P → Bool) :
    ((Fintype.piFinset (fun _ : Fin m => D)).filter
      (fun x => (fun i => g (x i)) = (fun i => f (x i)))).card =
      (D.filter (fun p => f p = g p)).card ^ m := by
  have : (Fintype.piFinset (fun _ : Fin m => D)).filter
      (fun x => (fun i => g (x i)) = (fun i => f (x i))) =
      Fintype.piFinset (fun _ : Fin m => D.filter (fun p => f p = g p)) := by
    ext x
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ i
      exact ⟨h1 i, (congrFun h2 i).symm⟩
    · intro h
      exact ⟨fun i => (h i).1, funext fun i => ((h i).2).symm⟩
  rw [this, Fintype.card_piFinset]
  simp

/-- one sample: the number of non-unique elements is at least `|T| - Γ`. -/
theorem core_x (F : Set (P → Bool)) (d : ℕ) (hVC : HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞))
    (T : Finset (P → Bool)) (hT : (↑T : Set (P → Bool)) ⊆ F) (m : ℕ) (x : Fin m → P) :
    T.card ≤ (∑ k ∈ Finset.range (d + 1), m.choose k) +
      (T.filter (fun f => ∃ g ∈ T, g ≠ f ∧ (fun i => g (x i)) = (fun i => f (x i)))).card := by
  set bad := T.filter (fun f => ∃ g ∈ T, g ≠ f ∧ (fun i => g (x i)) = (fun i => f (x i))) with hbad
  set good := T.filter (fun f => ¬ ∃ g ∈ T, g ≠ f ∧ (fun i => g (x i)) = (fun i => f (x i))) with hgood
  have h0 : bad.card + good.card = T.card := Finset.card_filter_add_card_filter_not _
  have hinj : Set.InjOn (fun f : P → Bool => fun i => f (x i)) (↑good : Set (P → Bool)) := by
    intro f hf g hg hfg
    by_contra hne
    have hf' := (Finset.mem_filter.1 hf)
    have hg' := (Finset.mem_filter.1 hg)
    exact hf'.2 ⟨g, hg'.1, fun h => hne h.symm, hfg.symm⟩
  have h1 : good.card = (good.image (fun f : P → Bool => fun i => f (x i))).card :=
    (Finset.card_image_of_injOn hinj).symm
  have h2 : (↑(good.image (fun f : P → Bool => fun i => f (x i))) : Set (Fin m → Bool)) ⊆
      trace F x := by
    intro y hy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy
    obtain ⟨f, hf, rfl⟩ := hy
    exact ⟨f, hT (Finset.mem_filter.1 hf).1, rfl⟩
  have h3 := Set.ncard_le_ncard h2 (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h3
  have h4 := Eq4b.sauer_trace F d m hVC x
  omega


theorem core (F : Set (P → Bool)) (d : ℕ) (hVC : HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞))
    (D : Finset P) (s : ℕ) (hs : s ≤ D.card)
    (T : Finset (P → Bool)) (hT : (↑T : Set (P → Bool)) ⊆ F)
    (hsep : ∀ f ∈ T, ∀ g ∈ T, f ≠ g → s ≤ dd D f g) (m : ℕ) :
    D.card ^ m * T.card ≤ D.card ^ m * (∑ k ∈ Finset.range (d + 1), m.choose k) +
      T.card * T.card * (D.card - s) ^ m := by
  set XS := Fintype.piFinset (fun _ : Fin m => D) with hXS
  have hXc : XS.card = D.card ^ m := by simp [hXS, Fintype.card_piFinset]
  set Γ := ∑ k ∈ Finset.range (d + 1), m.choose k with hΓ
  have hx : ∀ x ∈ XS, T.card ≤ Γ + ∑ f ∈ T, ∑ g ∈ T,
      (if g ≠ f ∧ (fun i => g (x i)) = (fun i => f (x i)) then 1 else 0) := by
    intro x _
    refine (core_x F d hVC T hT m x).trans ?_
    apply Nat.add_le_add_left
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro f hf
    by_cases h : ∃ g ∈ T, g ≠ f ∧ (fun i => g (x i)) = (fun i => f (x i))
    · obtain ⟨g, hg, hne, heq⟩ := h
      rw [if_pos ⟨g, hg, hne, heq⟩]
      refine le_trans ?_ (Finset.single_le_sum (f := fun g => (if g ≠ f ∧ (fun i => g (x i)) = (fun i => f (x i)) then 1 else 0)) (fun _ _ => Nat.zero_le _) hg)
      simp [hne, heq]
    · rw [if_neg h]; exact Nat.zero_le _
  have hsum := Finset.sum_le_sum hx
  rw [Finset.sum_const, hXc, smul_eq_mul] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_const, hXc, smul_eq_mul] at hsum
  have hswap : ∑ x ∈ XS, ∑ f ∈ T, ∑ g ∈ T,
      (if g ≠ f ∧ (fun i => g (x i)) = (fun i => f (x i)) then 1 else 0) =
      ∑ f ∈ T, ∑ g ∈ T, ∑ x ∈ XS,
      (if g ≠ f ∧ (fun i => g (x i)) = (fun i => f (x i)) then 1 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro f _
    rw [Finset.sum_comm]
  have hbound : ∑ f ∈ T, ∑ g ∈ T, ∑ x ∈ XS,
      (if g ≠ f ∧ (fun i => g (x i)) = (fun i => f (x i)) then 1 else 0) ≤
      ∑ f ∈ T, ∑ g ∈ T, (D.card - s) ^ m := by
    apply Finset.sum_le_sum; intro f hf
    apply Finset.sum_le_sum; intro g hg
    by_cases hgf : g = f
    · simp [hgf]
    · have h1 : ∑ x ∈ XS, (if g ≠ f ∧ (fun i => g (x i)) = (fun i => f (x i)) then 1 else 0) =
          (XS.filter (fun x => (fun i => g (x i)) = (fun i => f (x i)))).card := by
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl; intro x _
        simp [hgf]
      rw [h1, hXS, count_agree]
      apply Nat.pow_le_pow_left
      have h2 := agree_card D f g
      have h3 := hsep f hf g hg (fun h => hgf h.symm)
      omega
  simp only [Finset.sum_const, smul_eq_mul] at hbound
  rw [hswap] at hsum
  nlinarith [hsum, hbound]


theorem packing (F : Set (P → Bool)) (d : ℕ) (hVC : HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞))
    (D : Finset P) (s : ℕ) (hs1 : 1 ≤ s) (hs : s ≤ D.card)
    (T : Finset (P → Bool)) (hT : (↑T : Set (P → Bool)) ⊆ F)
    (hsep : ∀ f ∈ T, ∀ g ∈ T, f ≠ g → s ≤ dd D f g) (m : ℕ)
    (hm : (4 * ((∑ k ∈ Finset.range (d + 1), m.choose k : ℕ) : ℝ) + 2) ≤
      Real.exp (m * s / D.card)) :
    T.card ≤ 2 * ∑ k ∈ Finset.range (d + 1), m.choose k := by
  by_contra hlt
  push Not at hlt
  set Γ := ∑ k ∈ Finset.range (d + 1), m.choose k with hΓ
  obtain ⟨T', hT'T, hT'c⟩ := Finset.exists_subset_card_eq (s := T) (n := 2 * Γ + 1) (by omega)
  have hc := core F d hVC D s hs T' (fun f hf => hT (hT'T hf))
    (fun f hf g hg h => hsep f (hT'T hf) g (hT'T hg) h) m
  rw [hT'c] at hc
  have hnpos : (0 : ℝ) < D.card := by exact_mod_cast (hs1.trans hs)
  have hsR : (s : ℝ) ≤ D.card := by exact_mod_cast hs
  have hc' : ((D.card : ℝ)) ^ m * (2 * Γ + 1) ≤ (D.card : ℝ) ^ m * Γ + (2 * Γ + 1) * (2 * Γ + 1) * ((D.card : ℝ) - s) ^ m := by
    have := (Nat.cast_le (α := ℝ)).2 hc
    have hΓc : (Γ : ℝ) = ∑ x ∈ Finset.range (d + 1), (m.choose x : ℝ) := by
      rw [hΓ]; push_cast; rfl
    push_cast [Nat.cast_sub hs] at this
    rw [← hΓc] at this
    exact this
  have hu : ((D.card : ℝ) - s) * Real.exp (s / D.card) ≤ D.card := by
    have h1 : 1 - (s : ℝ) / D.card ≤ Real.exp (-(s / D.card)) := by
      linarith [Real.add_one_le_exp (-((s : ℝ) / D.card))]
    have h2 : ((D.card : ℝ) - s) = D.card * (1 - s / D.card) := by field_simp
    rw [h2, mul_assoc]
    have h3 : (1 - (s : ℝ) / D.card) * Real.exp (s / D.card) ≤ 1 := by
      calc (1 - (s : ℝ) / D.card) * Real.exp (s / D.card) ≤ Real.exp (-(s / D.card)) * Real.exp (s / D.card) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hE : Real.exp (m * s / D.card) = Real.exp (s / D.card) ^ m := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hpow : ((D.card : ℝ) - s) ^ m * Real.exp (m * s / D.card) ≤ (D.card : ℝ) ^ m := by
    rw [hE, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (by linarith) (Real.exp_pos _).le) hu m
  have hG : (0 : ℝ) ≤ Γ := Nat.cast_nonneg _
  have hpn : (0 : ℝ) < (D.card : ℝ) ^ m := by positivity
  have hE0 := Real.exp_pos (m * s / D.card)
  have hsub : (0 : ℝ) ≤ ((D.card : ℝ) - s) ^ m := pow_nonneg (by linarith) m
  -- (Γ+1) n^m ≤ (2Γ+1)^2 (n-s)^m, multiply by E
  have k1 : (Γ + 1 : ℝ) * (D.card : ℝ) ^ m ≤ (2 * Γ + 1) * (2 * Γ + 1) * ((D.card : ℝ) - s) ^ m := by
    nlinarith
  have k2 : (Γ + 1 : ℝ) * (D.card : ℝ) ^ m * Real.exp (m * s / D.card) ≤
      (2 * Γ + 1) * (2 * Γ + 1) * (((D.card : ℝ) - s) ^ m * Real.exp (m * s / D.card)) := by
    have := mul_le_mul_of_nonneg_right k1 hE0.le
    linarith
  have k3 : (Γ + 1 : ℝ) * (4 * Γ + 2) * (D.card : ℝ) ^ m ≤ (Γ + 1) * (D.card : ℝ) ^ m * Real.exp (m * s / D.card) := by
    have := mul_le_mul_of_nonneg_left hm (show (0:ℝ) ≤ (Γ + 1) * (D.card : ℝ) ^ m by positivity)
    linarith
  have k4 : (2 * Γ + 1) * (2 * Γ + 1) * (((D.card : ℝ) - s) ^ m * Real.exp (m * s / D.card)) ≤
      (2 * Γ + 1) * (2 * Γ + 1) * (D.card : ℝ) ^ m :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  nlinarith

end OptimalAgnosticPAC.Dev.Eq4c
end

section
open scoped Classical

namespace OptimalAgnosticPAC.Dev.Eq4d
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.Eq4c
variable {P : Type} [Fintype P]

theorem log6_le : Real.log 6 ≤ 2 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : (6 : ℝ) ≤ Real.exp 2 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  calc Real.log 6 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h2
    _ = 2 := Real.log_exp 2

/-- the analytic condition on `m`. -/
theorem m_cond (d : ℕ) (hd : 1 ≤ d) (u : ℝ) (hu : 1 ≤ u) (m : ℕ)
    (hm1 : (d : ℝ) * (5 + 1.3 * Real.log u) * u ≤ m)
    (hm2 : (m : ℝ) ≤ (d : ℝ) * (5 + 1.3 * Real.log u) * u + 1) :
    Real.log 6 + d * (1 + Real.log (m / d)) ≤ m / u := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : 0 ≤ Real.log u := Real.log_nonneg hu
  set x := Real.log u with hxdef
  set t : ℝ := 5 + 1.3 * x with ht
  have ht5 : 5 ≤ t := by rw [ht]; linarith
  have hmpos : (0 : ℝ) < m := by
    have : (0:ℝ) < d * t * u := by positivity
    linarith
  have hdu : (1 : ℝ) ≤ d * u := by nlinarith
  have h1 : (m : ℝ) / d ≤ (t + 1) * u := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h2 : Real.log (m / d) ≤ Real.log (6 + 1.3 * x) + x := by
    calc Real.log (m / d) ≤ Real.log ((t + 1) * u) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log (t + 1) + x := Real.log_mul (by linarith) (by linarith)
      _ = _ := by rw [ht]; congr 2; ring
  have h3 : Real.log (6 + 1.3 * x) ≤ Real.log 6 + 1.3 * x / 6 := by
    have : (6 + 1.3 * x) = 6 * (1 + 1.3 * x / 6) := by ring
    rw [this, Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1.3 * x / 6 by positivity)
    linarith
  have h4 : (d : ℝ) * t ≤ m / u := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have h5 := log6_le
  have h6 : (d : ℝ) * (1 + Real.log (m / d)) ≤ d * (1 + (Real.log 6 + 1.3 * x / 6 + x)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
  have h7 : (0 : ℝ) ≤ d * (x * 0.0833) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h5 (show (0:ℝ) ≤ d by linarith)]

theorem card_le_exp (F : Set (P → Bool)) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞))
    (D : Finset P) (s : ℕ) (hs1 : 1 ≤ s) (hs : s ≤ D.card)
    (T : Finset (P → Bool)) (hT : (↑T : Set (P → Bool)) ⊆ F)
    (hsep : ∀ f ∈ T, ∀ g ∈ T, f ≠ g → s ≤ dd D f g) :
    (T.card : ℝ) ≤ Real.exp (d * (5 + 1.3 * Real.log ((D.card : ℝ) / s)) + 1) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hnR : (s : ℝ) ≤ D.card := by exact_mod_cast hs
  set u : ℝ := (D.card : ℝ) / s with hu
  have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ (by linarith)]; linarith
  have hx : 0 ≤ Real.log u := Real.log_nonneg hu1
  set m : ℕ := ⌈(d : ℝ) * (5 + 1.3 * Real.log u) * u⌉₊ with hm
  have hm1 : (d : ℝ) * (5 + 1.3 * Real.log u) * u ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) ≤ (d : ℝ) * (5 + 1.3 * Real.log u) * u + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hc := m_cond d hd u hu1 m hm1 hm2
  have hdm : d ≤ m := by
    have : (d : ℝ) ≤ m := by
      have h5 : 1 ≤ (5 + 1.3 * Real.log u) * u := by nlinarith
      have h6 := mul_le_mul_of_nonneg_left h5 (show (0:ℝ) ≤ d by linarith)
      nlinarith [h6]
    exact_mod_cast this
  have hmR : (0 : ℝ) < m := by have : (1:ℝ) ≤ m := by exact_mod_cast hd.trans hdm
                               linarith
  have hS := Eq4b.sum_choose_le d m hd hdm
  have hG1 : (1 : ℝ) ≤ ∑ k ∈ Finset.range (d + 1), (m.choose k : ℝ) := by
    have : (1 : ℝ) ≤ (m.choose 0 : ℝ) := by simp
    refine this.trans ?_
    exact Finset.single_le_sum (f := fun k => (m.choose k : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      (Finset.mem_range.2 (Nat.succ_pos d))
  have hmu : (m : ℝ) * s / D.card = m / u := by rw [hu]; field_simp
  have hexp : (Real.exp 1 * m / d) ^ d = Real.exp (d * (1 + Real.log (m / d))) := by
    have : Real.exp 1 * m / d = Real.exp (1 + Real.log (m / d)) := by
      rw [Real.exp_add, Real.exp_log (by positivity)]; ring
    rw [this, ← Real.exp_nat_mul]
  have hcond : (4 * ((∑ k ∈ Finset.range (d + 1), m.choose k : ℕ) : ℝ) + 2) ≤
      Real.exp (m * s / D.card) := by
    push_cast
    rw [hmu]
    calc 4 * (∑ k ∈ Finset.range (d + 1), (m.choose k : ℝ)) + 2
        ≤ 6 * (Real.exp 1 * m / d) ^ d := by linarith
      _ = Real.exp (Real.log 6 + d * (1 + Real.log (m / d))) := by
          rw [hexp, Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.2 hc
  have hp := packing F d hVC D s hs1 hs T hT hsep m hcond
  have hp' : (T.card : ℝ) ≤ Real.exp (m * s / D.card) := by
    have : (T.card : ℝ) ≤ 2 * ((∑ k ∈ Finset.range (d + 1), m.choose k : ℕ) : ℝ) := by exact_mod_cast hp
    push_cast at this hcond
    linarith
  refine hp'.trans (Real.exp_le_exp.2 ?_)
  rw [hmu]
  have : (m : ℝ) / u ≤ ((d : ℝ) * (5 + 1.3 * Real.log u) * u + 1) / u := by
    gcongr
  refine this.trans ?_
  rw [add_div, mul_div_assoc, div_self (by linarith), mul_one]
  have : 1 / u ≤ 1 := by rw [div_le_one (by linarith)]; exact hu1
  linarith

end OptimalAgnosticPAC.Dev.Eq4d
end

section
open scoped Classical

namespace OptimalAgnosticPAC.Dev.Eq4e
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.Eq4c OptimalAgnosticPAC.Dev.Eq4a

variable {P : Type} [Fintype P]

/-- the inner product over `D` of the sign vectors -/
noncomputable def ip (D : Finset P) (ε g : P → Bool) : ℝ := ∑ p ∈ D, sgn (ε p) * sgn (g p)

theorem sgn_sq (a b : Bool) : (sgn a - sgn b) ^ 2 = if a ≠ b then 4 else 0 := by
  cases a <;> cases b <;> simp [sgn] <;> norm_num

theorem step (D : Finset P) (A B : Finset (P → Bool)) (hA : A.Nonempty) (hB : B.Nonempty) (ρ : ℕ)
    (hcov : ∀ g ∈ B, ∃ a ∈ A, dd D g a ≤ ρ) :
    avg (fun ε => B.sup' hB (ip D ε)) ≤
      avg (fun ε => A.sup' hA (ip D ε)) + 2 * Real.sqrt ρ * Real.sqrt (2 * Real.log B.card) := by
  choose! π hπA hπd using hcov
  set vec : (P → Bool) → P → ℝ := fun g p => if p ∈ D then sgn (g p) - sgn (π g p) else 0 with hvec
  set G : Finset (P → ℝ) := B.image vec with hG
  have hGne : G.Nonempty := hB.image _
  have hpt : ∀ ε : P → Bool, B.sup' hB (ip D ε) ≤
      A.sup' hA (ip D ε) + G.sup' hGne (fun h => ∑ p, sgn (ε p) * h p) := by
    intro ε
    refine Finset.sup'_le _ _ fun g hg => ?_
    have e : ip D ε g = ip D ε (π g) + ∑ p, sgn (ε p) * vec g p := by
      simp only [ip, hvec, mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro p _; ring
    rw [e]
    have h1 : ip D ε (π g) ≤ A.sup' hA (ip D ε) := Finset.le_sup' (ip D ε) (hπA g hg)
    have h2 : ∑ p, sgn (ε p) * vec g p ≤ G.sup' hGne (fun h => ∑ p, sgn (ε p) * h p) :=
      Finset.le_sup' (fun h => ∑ p, sgn (ε p) * h p) (Finset.mem_image_of_mem vec hg)
    linarith
  have h1 := avg_mono hpt
  rw [avg_add] at h1
  have hvar : ∀ h ∈ G, ∑ p, h p ^ 2 ≤ (2 * Real.sqrt ρ) ^ 2 := by
    intro h hh
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hh
    have : ∑ p, vec g p ^ 2 = 4 * (dd D g (π g) : ℝ) := by
      simp only [hvec, dd]
      rw [Finset.card_filter]
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => p ∈ D)]
      have z : ∑ p ∈ Finset.univ.filter (fun p => p ∉ D), (if p ∈ D then sgn (g p) - sgn (π g p) else 0) ^ 2 = 0 := by
        apply Finset.sum_eq_zero; intro p hp; simp at hp; simp [hp]
      rw [z, add_zero]
      have : Finset.univ.filter (fun p => p ∈ D) = D := by ext; simp
      rw [this]
      apply Finset.sum_congr rfl; intro p hp
      rw [if_pos hp, sgn_sq]; split_ifs <;> simp
    rw [this, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    have := hπd g hg
    have : (dd D g (π g) : ℝ) ≤ ρ := by exact_mod_cast this
    nlinarith
  have hM := massart G hGne (2 * Real.sqrt ρ) (by positivity) hvar
  have hcard1 : (1 : ℝ) ≤ G.card := by exact_mod_cast hGne.card_pos
  have hle : (G.card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_image_le
  have hlog : Real.log G.card ≤ Real.log B.card := Real.log_le_log (by linarith) hle
  have hsq : Real.sqrt (2 * Real.log G.card) ≤ Real.sqrt (2 * Real.log B.card) :=
    Real.sqrt_le_sqrt (by linarith)
  calc _ ≤ _ := h1
    _ ≤ avg (fun ε => A.sup' hA (ip D ε)) + 2 * Real.sqrt ρ * Real.sqrt (2 * Real.log B.card) := by
      have := mul_le_mul_of_nonneg_left hsq (show (0:ℝ) ≤ 2 * Real.sqrt ρ by positivity)
      linarith

/-- maximal separated subsets are nets -/
theorem net_exists (F : Set (P → Bool)) (hF : F.Nonempty) (D : Finset P) (s : ℕ) (hs : 1 ≤ s) :
    ∃ N : Finset (P → Bool), (↑N : Set (P → Bool)) ⊆ F ∧
      (∀ f ∈ N, ∀ g ∈ N, f ≠ g → s ≤ dd D f g) ∧ (∀ f ∈ F, ∃ g ∈ N, dd D f g < s) := by
  set S : Finset (Finset (P → Bool)) := Finset.univ.filter (fun N =>
    (↑N : Set (P → Bool)) ⊆ F ∧ ∀ f ∈ N, ∀ g ∈ N, f ≠ g → s ≤ dd D f g) with hS
  have hne : S.Nonempty := ⟨∅, by simp [hS]⟩
  obtain ⟨N, hNS, hmax⟩ := Finset.exists_max_image S Finset.card hne
  have hN := (Finset.mem_filter.1 hNS).2
  refine ⟨N, hN.1, hN.2, fun f hf => ?_⟩
  by_contra hcon
  push Not at hcon
  have hfN : f ∉ N := fun h => by
    have := hcon f h; rw [dd_self] at this; omega
  have : insert f N ∈ S := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | h
      · exact hf
      · exact hN.1 h
    · intro a ha b hb hab
      rcases Finset.mem_insert.1 ha with rfl | ha' <;> rcases Finset.mem_insert.1 hb with rfl | hb'
      · exact absurd rfl hab
      · exact hcon b hb'
      · rw [dd_symm]; exact hcon a ha'
      · exact hN.2 a ha' b hb' hab
  have := hmax _ this
  rw [Finset.card_insert_of_notMem hfN] at this
  omega

end OptimalAgnosticPAC.Dev.Eq4e
end

section
open scoped Classical

namespace OptimalAgnosticPAC.Dev.Eq4f
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.Eq4c OptimalAgnosticPAC.Dev.Eq4a
  OptimalAgnosticPAC.Dev.Eq4e

variable {P : Type} [Fintype P]

noncomputable def rho' (n K j : ℕ) : ℕ := if j = 0 then n else 2 ^ (K - j)

noncomputable def LL (d : ℕ) (j : ℕ) : ℝ := d * (5 + 0.91 * j) + 1

noncomputable def Bk (d n K : ℕ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => Bk d n K j + 2 * Real.sqrt (rho' n K j) * Real.sqrt (2 * LL d (j + 1))

theorem avg_sgn (p : P) : avg (fun ε : P → Bool => sgn (ε p)) = 0 := by
  have := avg_prod (fun q b => if q = p then sgn b else 1)
  have e : ∀ ε : P → Bool, (∏ q, (fun q b => if q = p then sgn b else 1) q (ε q)) = sgn (ε p) := by
    intro ε; simp
  simp only [e] at this
  rw [this]
  apply Finset.prod_eq_zero (Finset.mem_univ p)
  simp [sgn]

theorem avg_ip_single (D : Finset P) (f : P → Bool) : avg (fun ε => ip D ε f) = 0 := by
  unfold ip
  rw [avg_sum]
  apply Finset.sum_eq_zero; intro p _
  have : (fun ε : P → Bool => sgn (ε p) * sgn (f p)) = fun ε => sgn (f p) * sgn (ε p) := by
    funext ε; ring
  rw [this, avg_mul_left, avg_sgn, mul_zero]

theorem chain (F : Set (P → Bool)) (hF : F.Nonempty) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞)) (D : Finset P) (hn : 1 ≤ D.card) (K : ℕ)
    (hK1 : D.card < 2 ^ K) (hK2 : 2 ^ (K - 1) ≤ D.card) :
    ∀ J, J ≤ K → ∃ (N : Finset (P → Bool)) (hN : N.Nonempty), (↑N : Set (P → Bool)) ⊆ F ∧
      (∀ f ∈ F, ∃ g ∈ N, dd D f g ≤ rho' D.card K J ∧ (1 ≤ J → dd D f g < 2 ^ (K - J))) ∧
      avg (fun ε => N.sup' hN (ip D ε)) ≤ Bk d D.card K J := by
  intro J
  induction J with
  | zero =>
    intro _
    obtain ⟨f0, hf0⟩ := hF
    refine ⟨{f0}, Finset.singleton_nonempty _, by simpa using hf0, ?_, ?_⟩
    · intro f _
      refine ⟨f0, Finset.mem_singleton_self _, ?_, by intro h; omega⟩
      simp only [rho', if_true, dd]
      exact Finset.card_filter_le _ _
    · simp only [Finset.sup'_singleton, Bk]
      rw [avg_ip_single]
  | succ J ih =>
    intro hJ
    obtain ⟨N, hN, hNF, hcov, hbd⟩ := ih (by omega)
    have hs1 : 1 ≤ 2 ^ (K - (J + 1)) := Nat.one_le_two_pow
    have hsn : 2 ^ (K - (J + 1)) ≤ D.card :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hK2
    obtain ⟨N', hN'F, hN'sep, hN'cov⟩ := Eq4e.net_exists F hF D _ hs1
    have hN'ne : N'.Nonempty := by
      obtain ⟨f0, hf0⟩ := hF
      obtain ⟨g, hg, _⟩ := hN'cov f0 hf0
      exact ⟨g, hg⟩
    refine ⟨N', hN'ne, hN'F, ?_, ?_⟩
    · intro f hf
      obtain ⟨g, hg, h⟩ := hN'cov f hf
      refine ⟨g, hg, ?_, fun _ => h⟩
      simp only [rho']; rw [if_neg (by omega)]; exact h.le
    · have hst := Eq4e.step D N N' hN hN'ne (rho' D.card K J) (fun g hg => by
        obtain ⟨a, ha, h, _⟩ := hcov g (hN'F hg)
        exact ⟨a, ha, h⟩)
      have hcard := Eq4d.card_le_exp F d hd hVC D _ hs1 hsn N' hN'F hN'sep
      have hc1 : (1 : ℝ) ≤ N'.card := by exact_mod_cast hN'ne.card_pos
      have hlog : Real.log N'.card ≤ LL d (J + 1) := by
        have h1 : Real.log N'.card ≤ d * (5 + 1.3 * Real.log ((D.card : ℝ) / (2 ^ (K - (J + 1)) : ℕ))) + 1 := by
          have := Real.log_le_log (by linarith) hcard
          rwa [Real.log_exp] at this
        refine h1.trans ?_
        unfold LL
        have hr : (D.card : ℝ) / (2 ^ (K - (J + 1)) : ℕ) ≤ 2 ^ (J + 1) := by
          rw [div_le_iff₀ (by positivity)]
          have : (D.card : ℝ) ≤ 2 ^ K := by exact_mod_cast hK1.le
          have e : (2 : ℝ) ^ K = 2 ^ (J + 1) * (2 ^ (K - (J + 1)) : ℕ) := by
            push_cast; rw [← pow_add]; congr 1; omega
          rw [e] at this; exact this
        have hl : Real.log ((D.card : ℝ) / (2 ^ (K - (J + 1)) : ℕ)) ≤ (J + 1) * Real.log 2 := by
          calc _ ≤ Real.log (2 ^ (J + 1)) := Real.log_le_log (by positivity) hr
            _ = _ := by rw [Real.log_pow]; push_cast; ring
        have hl2 := Real.log_two_lt_d9
        have hdR : (0:ℝ) ≤ d := by positivity
        have : 1.3 * Real.log ((D.card : ℝ) / (2 ^ (K - (J + 1)) : ℕ)) ≤ 0.91 * ((J + 1 : ℕ) : ℝ) := by
          push_cast at hl ⊢; nlinarith [hl, hl2, mul_nonneg (show (0:ℝ) ≤ (J:ℝ) + 1 by positivity) (show (0:ℝ) ≤ 0.6931471808 - Real.log 2 by linarith)]
        have := mul_le_mul_of_nonneg_left (add_le_add_left this 5) hdR
        linarith
      have hsq : Real.sqrt (2 * Real.log N'.card) ≤ Real.sqrt (2 * LL d (J + 1)) :=
        Real.sqrt_le_sqrt (by linarith)
      have := mul_le_mul_of_nonneg_left hsq (show (0:ℝ) ≤ 2 * Real.sqrt (rho' D.card K J) by positivity)
      simp only [Bk]
      linarith

theorem width_le_Bk (F : Set (P → Bool)) (hF : F.Nonempty) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞)) (D : Finset P) (hn : 1 ≤ D.card) (K : ℕ)
    (hK1 : D.card < 2 ^ K) (hK2 : 2 ^ (K - 1) ≤ D.card) :
    width F D ≤ Bk d D.card K K := by
  obtain ⟨N, hN, hNF, hcov, hbd⟩ := chain F hF d hd hVC D hn K hK1 hK2 K le_rfl
  have hK : 1 ≤ K := by
    by_contra h; have : K = 0 := by omega
    subst this; rw [pow_zero] at hK1; omega
  refine le_trans ?_ hbd
  unfold width
  change avg _ ≤ _
  apply avg_mono
  intro ε
  obtain ⟨f0, hf0⟩ := hF
  apply csSup_le (Set.Nonempty.image _ ⟨f0, hf0⟩)
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨g, hg, _, hlt⟩ := hcov f hf
  have h0 : dd D f g = 0 := by have := hlt hK; simp at this; exact this
  have hag : ∀ p ∈ D, f p = g p := by
    intro p hp
    by_contra h
    have : p ∈ D.filter (fun p => f p ≠ g p) := by simp [hp, h]
    have : 0 < dd D f g := Finset.card_pos.2 ⟨p, this⟩
    omega
  have : ip D ε f = ip D ε g := Finset.sum_congr rfl fun p hp => by rw [hag p hp]
  show ip D ε f ≤ _
  rw [this]
  exact Finset.le_sup' (ip D ε) hg

end OptimalAgnosticPAC.Dev.Eq4f
end

section
open scoped Classical

namespace OptimalAgnosticPAC.Dev.Eq4g
open OptimalAgnosticPAC.Dev.Eq4f

theorem term_bound (d n K J : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hK : 2 ^ K ≤ 2 * n) (hJ1 : 1 ≤ J)
    (hJ : J ≤ K) :
    2 * Real.sqrt (rho' n K J) * Real.sqrt (2 * LL d (J + 1)) ≤
      4 * Real.sqrt (d * n) * (0.71 ^ J * (2.72 + 0.134 * J)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hρ : (rho' n K J : ℝ) = 2 ^ (K - J) := by
    simp only [rho']; rw [if_neg (by omega)]; push_cast; rfl
  have hρle : (rho' n K J : ℝ) ≤ 2 * n * (0.71 ^ J) ^ 2 := by
    rw [hρ]
    have h1 : (2 : ℝ) ^ (K - J) * 2 ^ J = 2 ^ K := by rw [← pow_add]; congr 1; omega
    have h2 : (2 : ℝ) ^ K ≤ 2 * n := by exact_mod_cast hK
    have h3 : ((1 : ℝ) / 2) ^ J ≤ (0.71 ^ J) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      apply pow_le_pow_left₀ (by norm_num); norm_num
    have h4 : (2 : ℝ) ^ (K - J) ≤ 2 * n * ((1 : ℝ) / 2) ^ J := by
      have : ((1 : ℝ) / 2) ^ J * 2 ^ J = 1 := by rw [← mul_pow]; norm_num
      have hp : (0:ℝ) < 2 ^ J := by positivity
      calc (2 : ℝ) ^ (K - J) = 2 ^ (K - J) * (2 ^ J * ((1:ℝ)/2) ^ J) := by rw [mul_comm ((2:ℝ)^J), this, mul_one]
        _ = (2 ^ (K - J) * 2 ^ J) * ((1:ℝ)/2) ^ J := by ring
        _ ≤ 2 * n * ((1:ℝ)/2) ^ J := by rw [h1]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
    calc _ ≤ _ := h4
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hLL : LL d (J + 1) ≤ d * (6.91 + 0.91 * J) := by
    unfold LL; push_cast; nlinarith
  have hq : (0 : ℝ) ≤ 0.71 ^ J := by positivity
  set q := (0.71 : ℝ) ^ J with hqdef
  set Y := 4 * Real.sqrt (d * n) * (q * (2.72 + 0.134 * J)) with hY
  have hJR : (0 : ℝ) ≤ J := by positivity
  have hYnn : 0 ≤ Y := by rw [hY]; positivity
  have hX : 0 ≤ 2 * Real.sqrt (rho' n K J) * Real.sqrt (2 * LL d (J + 1)) := by positivity
  apply le_of_pow_le_pow_left₀ (two_ne_zero) hYnn
  have hs2 : Real.sqrt (d * n) ^ 2 = d * n := Real.sq_sqrt (by positivity)
  have hLLnn : (0:ℝ) ≤ LL d (J + 1) := by unfold LL; positivity
  have e1 : (2 * Real.sqrt (rho' n K J) * Real.sqrt (2 * LL d (J + 1))) ^ 2 = 8 * rho' n K J * LL d (J + 1) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (by positivity)]; ring
  have e2 : Y ^ 2 = 16 * (d * n) * q ^ 2 * (2.72 + 0.134 * J) ^ 2 := by
    rw [hY, mul_pow, mul_pow, hs2]; ring
  rw [e1, e2]
  have hq2 : 0 ≤ q ^ 2 := by positivity
  have hρnn : (0:ℝ) ≤ rho' n K J := Nat.cast_nonneg _
  have k1 : 8 * (rho' n K J : ℝ) * LL d (J + 1) ≤ 8 * (2 * n * q ^ 2) * (d * (6.91 + 0.91 * J)) := by
    apply mul_le_mul (by linarith) hLL hLLnn (by positivity)
  have k2 : (6.91 + 0.91 * (J : ℝ)) ≤ (2.72 + 0.134 * J) ^ 2 := by nlinarith [sq_nonneg ((J : ℝ) - 5)]
  have k3 : 8 * (2 * (n : ℝ) * q ^ 2) * (d * (6.91 + 0.91 * J)) ≤ 8 * (2 * n * q ^ 2) * (d * (2.72 + 0.134 * J) ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left k2 (by positivity)) (by positivity)
  nlinarith [k1, k3]


theorem Bk_le (d n K : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hK : 2 ^ K ≤ 2 * n) :
    ∀ J, 1 ≤ J → J ≤ K → Bk d n K J ≤
      Real.sqrt (d * n) * (7.5 + 4 * (7.86 - 0.71 ^ J * (10.6 + 0.47 * J))) := by
  intro J
  induction J with
  | zero => intro h; omega
  | succ J ih =>
    intro _ hJK
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · simp only [Bk, rho', if_true, zero_add]
      have h1 : Real.sqrt (2 * LL d 1) ≤ 3.72 * Real.sqrt d := by
        rw [Real.sqrt_le_left (by positivity)]
        unfold LL; push_cast; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ d by positivity), Real.sqrt_nonneg (d:ℝ)]
      have h2 : Real.sqrt (d * n) = Real.sqrt d * Real.sqrt n := Real.sqrt_mul (by positivity) _
      rw [h2]
      have := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 2 * Real.sqrt n by positivity)
      have h3 : (0:ℝ) ≤ Real.sqrt d * Real.sqrt n := by positivity
      have c : (7.5:ℝ) ≤ 7.5 + 4 * (7.86 - 0.71 ^ (0 + 1) * (10.6 + 0.47 * ((0 + 1 : ℕ) : ℝ))) := by norm_num
      nlinarith [this, h3, mul_le_mul_of_nonneg_left c h3]
    · have h1 := ih hJ (by omega)
      have h2 := term_bound d n K J hd hn hK hJ (by omega)
      simp only [Bk]
      have hs : (0:ℝ) ≤ Real.sqrt (d * n) := Real.sqrt_nonneg _
      have hq : (0:ℝ) ≤ 0.71 ^ J := by positivity
      have hJR : (0:ℝ) ≤ J := by positivity
      have e : (0.71:ℝ) ^ (J + 1) = 0.71 ^ J * 0.71 := pow_succ _ _
      have k : 0.71 ^ J * (2.72 + 0.134 * J) ≤ 0.71 ^ J * (10.6 + 0.47 * J) - 0.71 ^ (J + 1) * (10.6 + 0.47 * ((J + 1 : ℕ) : ℝ)) := by
        rw [e]; push_cast; nlinarith [mul_nonneg hq hJR]
      have := mul_le_mul_of_nonneg_left k (show (0:ℝ) ≤ 4 * Real.sqrt (d * n) by positivity)
      nlinarith [h1, h2, this]

end OptimalAgnosticPAC.Dev.Eq4g
end

section
open scoped Classical

namespace OptimalAgnosticPAC.Learner

/-- Equation (4), PDF p. 3: `R_D(F) ≤ 60 √(d|D|)`. -/
theorem chk_eq_4_rademacher_width {P : Type} [Fintype P] [Nonempty P] (d : ℕ) (hd : 1 ≤ d)
    (F : Set (P → Bool)) (hF : F.Nonempty) (hVC : HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞))
    (D : Finset P) :
    width F D ≤ 60 * Real.sqrt ((d : ℝ) * (D.card : ℝ)) := by
  rcases Nat.eq_zero_or_pos D.card with h0 | hpos
  · have hD : D = ∅ := Finset.card_eq_zero.1 h0
    subst hD
    unfold width
    simp only [Finset.sum_empty, mul_zero, Set.Nonempty.image_const hF, csSup_singleton,
      Finset.sum_const, Finset.card_univ, smul_zero, Finset.card_empty, Nat.cast_zero,
      Real.sqrt_zero, le_refl]
  · set n := D.card with hn
    set K := Nat.size n with hK
    have hK1 : n < 2 ^ K := Nat.lt_size_self n
    have hKpos : 1 ≤ K := by
      by_contra h
      have : K = 0 := by omega
      rw [this, pow_zero] at hK1; omega
    have hK2 : 2 ^ (K - 1) ≤ n := by
      by_contra h
      push Not at h
      have := Nat.size_le.2 h
      omega
    have hK3 : 2 ^ K ≤ 2 * n := by
      have : 2 ^ K = 2 * 2 ^ (K - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    have h1 := OptimalAgnosticPAC.Dev.Eq4f.width_le_Bk F hF d hd hVC D hpos K hK1 hK2
    have h2 := OptimalAgnosticPAC.Dev.Eq4g.Bk_le d n K hd hpos hK3 K hKpos le_rfl
    have hs : (0 : ℝ) ≤ Real.sqrt (d * n) := Real.sqrt_nonneg _
    have hq : (0 : ℝ) ≤ 0.71 ^ K * (10.6 + 0.47 * K) := by positivity
    have h3 : Real.sqrt (d * n) * (7.5 + 4 * (7.86 - 0.71 ^ K * (10.6 + 0.47 * K))) ≤
        Real.sqrt (d * n) * 60 := by
      apply mul_le_mul_of_nonneg_left _ hs; linarith
    simp only [hn] at *
    linarith

end OptimalAgnosticPAC.Learner

end

theorem solution : type_of% @OptimalAgnosticPAC.Learner.chk_eq_4_rademacher_width := @OptimalAgnosticPAC.Learner.chk_eq_4_rademacher_width
