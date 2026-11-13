-- Prove2me | solution 1 for RestrictedAP.Counting.claim_5_14_monotone
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:20:27.690197+00:00
-- url     : https://prove2.me/submissions/dfc63c81-deae-4a10-a89a-e9584f46ce18

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_Resilience

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RestrictedAP.Counting.Dev.C514
open RestrictedAP.Counting

/-! ## Generic facts about product weights on `Fin n → T` -/

section Generic

variable {T : Type} [Fintype T] [DecidableEq T] {n : ℕ}

/-- `mix I v x`: the vector equal to `v` on `I` and to `x` off `I`. -/
def mix (I : Finset (Fin n)) (v x : Fin n → T) : Fin n → T := fun i => if i ∈ I then v i else x i

theorem tensorPow_nonneg (w : T → ℝ) (hw : ∀ a, 0 ≤ w a) (x : Fin n → T) :
    0 ≤ tensorPow w n x :=
  Finset.prod_nonneg fun i _ => hw (x i)

theorem sum_tensorPow (w : T → ℝ) (hw1 : ∑ a, w a = 1) :
    ∑ x : Fin n → T, tensorPow w n x = 1 := by
  have h2 := Fintype.prod_sum (fun (_ : Fin n) (a : T) => w a)
  unfold tensorPow
  rw [← h2, hw1, Finset.prod_const_one]

/-- Mass of the vectors agreeing with `y` on `J`: `∏_{i ∈ J} w (y i)`. -/
theorem mass (w : T → ℝ) (hw1 : ∑ a, w a = 1) (J : Finset (Fin n)) (y : Fin n → T) :
    ∑ u : Fin n → T, (if ∀ i ∈ J, u i = y i then tensorPow w n u else 0) =
      ∏ i ∈ J, w (y i) := by
  have h1 : ∀ u : Fin n → T, (if ∀ i ∈ J, u i = y i then tensorPow w n u else 0) =
      ∏ i, (if i ∈ J then (if u i = y i then w (u i) else 0) else w (u i)) := by
    intro u
    unfold tensorPow
    split_ifs with h
    · refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i ∈ J <;> simp [hi, h i]
    · push_neg at h
      obtain ⟨i, hi, hne⟩ := h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hne])
  rw [Finset.sum_congr rfl fun u _ => h1 u]
  have h2 := Fintype.prod_sum
    (fun (i : Fin n) (a : T) => if i ∈ J then (if a = y i then w a else 0) else w a)
  rw [← h2]
  have h3 : ∀ i : Fin n, (∑ a : T, (if i ∈ J then (if a = y i then w a else 0) else w a)) =
      if i ∈ J then w (y i) else 1 := by
    intro i
    by_cases hi : i ∈ J <;> simp [hi, hw1]
  rw [Finset.prod_congr rfl fun i _ => h3 i, Finset.prod_ite_mem, Finset.univ_inter]

/-- Law of total expectation: average over the values `u` on `J` of the restricted averages. -/
theorem total (w : T → ℝ) (hw1 : ∑ a, w a = 1) (J : Finset (Fin n)) (g : (Fin n → T) → ℝ) :
    ∑ u, tensorPow w n u * ∑ x, tensorPow w n x * g (mix J u x) =
      ∑ y, tensorPow w n y * g y := by
  have hpt : ∀ u x : Fin n → T, tensorPow w n u * (tensorPow w n x * g (mix J u x)) =
      ∑ y, (if ∀ i ∈ J, u i = y i then tensorPow w n u else 0) *
        (if ∀ i ∈ Jᶜ, x i = y i then tensorPow w n x else 0) * g y := by
    intro u x
    rw [Finset.sum_eq_single (mix J u x)]
    · have h1 : ∀ i ∈ J, u i = mix J u x i := fun i hi => by simp [mix, hi]
      have h2 : ∀ i ∈ Jᶜ, x i = mix J u x i := fun i hi => by
        rw [Finset.mem_compl] at hi; simp [mix, hi]
      rw [if_pos h1, if_pos h2]; ring
    · intro y _ hy
      by_cases h1 : ∀ i ∈ J, u i = y i
      · by_cases h2 : ∀ i ∈ Jᶜ, x i = y i
        · exfalso; apply hy; funext i
          by_cases hi : i ∈ J
          · simp [mix, hi, h1 i hi]
          · simp [mix, hi, h2 i (Finset.mem_compl.mpr hi)]
        · rw [if_neg h2]; ring
      · rw [if_neg h1]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  have hy : ∀ y : Fin n → T,
      ∑ u, ∑ x, (if ∀ i ∈ J, u i = y i then tensorPow w n u else 0) *
        (if ∀ i ∈ Jᶜ, x i = y i then tensorPow w n x else 0) * g y =
      tensorPow w n y * g y := by
    intro y
    calc ∑ u, ∑ x, (if ∀ i ∈ J, u i = y i then tensorPow w n u else 0) *
          (if ∀ i ∈ Jᶜ, x i = y i then tensorPow w n x else 0) * g y
        = (∑ u, (if ∀ i ∈ J, u i = y i then tensorPow w n u else 0)) *
          (∑ x, (if ∀ i ∈ Jᶜ, x i = y i then tensorPow w n x else 0)) * g y := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_mul]
      _ = (∏ i ∈ J, w (y i)) * (∏ i ∈ Jᶜ, w (y i)) * g y := by
          rw [mass w hw1, mass w hw1]
      _ = tensorPow w n y * g y := by
          rw [Finset.prod_mul_prod_compl]; rfl
  calc ∑ u, tensorPow w n u * ∑ x, tensorPow w n x * g (mix J u x)
      = ∑ u, ∑ x, ∑ y, (if ∀ i ∈ J, u i = y i then tensorPow w n u else 0) *
          (if ∀ i ∈ Jᶜ, x i = y i then tensorPow w n x else 0) * g y := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => hpt u x
    _ = ∑ y, ∑ u, ∑ x, (if ∀ i ∈ J, u i = y i then tensorPow w n u else 0) *
          (if ∀ i ∈ Jᶜ, x i = y i then tensorPow w n x else 0) * g y := by
        exact (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ y, tensorPow w n y * g y := Finset.sum_congr rfl fun y _ => hy y

theorem mix_eq_of_agree (I : Finset (Fin n)) (u c x : Fin n → T) (h : ∀ i ∈ I, u i = c i) :
    mix I u x = mix I c x := by
  funext i
  by_cases hi : i ∈ I <;> simp [mix, hi, h i]

theorem mix_mix (I I' : Finset (Fin n)) (v u x : Fin n → T) :
    mix I v (mix I' u x) = mix (I ∪ I') (mix I v u) x := by
  funext i
  by_cases hi : i ∈ I <;> by_cases hi' : i ∈ I' <;> simp [mix, hi, hi']

theorem mix_empty (v x : Fin n → T) : mix ∅ v x = x := by
  funext i; simp [mix]

end Generic

/-! ## Abstract averaging facts -/

theorem sum_ge_of_const {U : Type} [Fintype U] (P H : U → ℝ) (hP : ∀ u, 0 ≤ P u)
    (hH : ∀ u, 0 ≤ H u) (A : U → Prop) [DecidablePred A] (c : ℝ) (hc : ∀ u, A u → H u = c) :
    (∑ u, if A u then P u else 0) * c ≤ ∑ u, P u * H u := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun u _ => ?_
  split_ifs with h
  · rw [hc u h]
  · rw [zero_mul]; exact mul_nonneg (hP u) (hH u)

/-- If the `A`-part (mass `p > 0`) has average `< d/2`, some value has average
`≥ d (1 + p/2)`. -/
theorem increment {U : Type} [Fintype U] (P h : U → ℝ) (hP : ∀ u, 0 ≤ P u)
    (hP1 : ∑ u, P u = 1) (A : U → Prop) [DecidablePred A] (w : U)
    (hw : ∀ u, A u → h u = h w) (p : ℝ) (hp : (∑ u, if A u then P u else 0) = p)
    (hp0 : 0 < p) (d : ℝ) (hd : d = ∑ u, P u * h u) (hd0 : 0 ≤ d) (hsmall : h w < d / 2) :
    ∃ u, d * (1 + p / 2) ≤ h u := by
  by_contra hcon
  push_neg at hcon
  set M := d * (1 + p / 2) with hM
  have h1 : ∑ u, P u * h u ≤ ∑ u, (P u * M + (if A u then P u * (h w - M) else 0)) := by
    refine Finset.sum_le_sum fun u _ => ?_
    split_ifs with hu
    · rw [hw u hu]
      have : P u * M + P u * (h w - M) = P u * h w := by ring
      rw [this]
    · rw [add_zero]; exact mul_le_mul_of_nonneg_left (hcon u).le (hP u)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hP1] at h1
  have h2 : ∑ u, (if A u then P u * (h w - M) else 0) = p * (h w - M) := by
    rw [← hp, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs <;> simp
  rw [h2, ← hd] at h1
  have h3 : p * h w < p * (d / 2) := mul_lt_mul_of_pos_left hsmall hp0
  have h4 : p * M = p * d + p * p * d / 2 := by rw [hM]; ring
  have h5 : 0 ≤ p * p * d := mul_nonneg (mul_nonneg hp0.le hp0.le) hd0
  nlinarith

/-! ## The setting of Claim 5.14 -/

section Setting

variable {Sig : Type} [Fintype Sig] [DecidableEq Sig]

theorem nu_ge (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ) (hμ : IsDist μ)
    (hmarg : ∀ i : Fin 3, marginal μ i = ν) (x : Sig) : μ (x, x, x) ≤ ν x := by
  rw [← hmarg 0]
  unfold marginal
  have := Finset.single_le_sum (f := fun t : Sig × Sig × Sig => if coord3 0 t = x then μ t else 0)
    (fun t _ => by split_ifs; exacts [hμ.1 t, le_refl 0])
    (Finset.mem_univ (x, x, x))
  simpa [coord3] using this

theorem nu_sum (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ) (hμ : IsDist μ)
    (hmarg : ∀ i : Fin 3, marginal μ i = ν) : ∑ x, ν x = 1 := by
  rw [← hmarg 0]
  unfold marginal
  rw [Finset.sum_comm]
  simpa using hμ.2

theorem expect_le_one {n : ℕ} (ν : Sig → ℝ) (hν : ∀ a, 0 ≤ ν a) (hν1 : ∑ a, ν a = 1)
    (g : (Fin n → Sig) → ℝ) (hg : ∀ x, g x = 0 ∨ g x = 1) : expect (tensorPow ν n) g ≤ 1 := by
  have h1 : ∑ x : Fin n → Sig, tensorPow ν n x = 1 := sum_tensorPow ν hν1
  unfold expect
  rw [← h1]
  refine Finset.sum_le_sum fun x _ => ?_
  rcases hg x with h | h <;> simp [h, tensorPow_nonneg ν hν x]

theorem Delta1_nonneg {n : ℕ} (μ : Sig × Sig × Sig → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (g : (Fin n → Sig) → ℝ) (hg : ∀ x, g x = 0 ∨ g x = 1) : 0 ≤ Delta1 μ g := by
  have hg0 : ∀ x, 0 ≤ g x := fun x => by rcases hg x with h | h <;> simp [h]
  unfold Delta1
  exact Finset.sum_nonneg fun t _ => mul_nonneg (tensorPow_nonneg μ hμ t)
    (mul_nonneg (mul_nonneg (hg0 _) (hg0 _)) (hg0 _))

/-- Restriction lemma: `Δ₁(f) ≥ α^{|I|} Δ₁(f_{I→v})`. -/
theorem delta1_restrict {n : ℕ} (μ : Sig × Sig × Sig → ℝ) (hμ : IsDist μ) (α : ℝ)
    (hα0 : 0 ≤ α) (hαμ : ∀ x, α ≤ μ (x, x, x)) (I : Finset (Fin n)) (v : Fin n → Sig)
    (f : (Fin n → Sig) → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) :
    α ^ I.card * Delta1 μ (fun x => f (mix I v x)) ≤ Delta1 μ f := by
  have hf0 : ∀ x, 0 ≤ f x := fun x => by rcases hf x with h | h <;> simp [h]
  set G : (Fin n → Sig × Sig × Sig) → ℝ := fun t =>
    f (fun i => (t i).1) * f (fun i => (t i).2.1) * f (fun i => (t i).2.2) with hG
  have hG0 : ∀ t, 0 ≤ G t := fun t => mul_nonneg (mul_nonneg (hf0 _) (hf0 _)) (hf0 _)
  let c : Fin n → Sig × Sig × Sig := fun i => (v i, v i, v i)
  have hDf : Delta1 μ f = ∑ y, tensorPow μ n y * G y := rfl
  have hDr : Delta1 μ (fun x => f (mix I v x)) =
      ∑ x, tensorPow μ n x * G (mix I c x) := by
    unfold Delta1
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : mix I v (fun i => (t i).1) = fun i => (mix I c t i).1 := by
      funext i; by_cases hi : i ∈ I <;> simp [mix, hi, c]
    have e2 : mix I v (fun i => (t i).2.1) = fun i => (mix I c t i).2.1 := by
      funext i; by_cases hi : i ∈ I <;> simp [mix, hi, c]
    have e3 : mix I v (fun i => (t i).2.2) = fun i => (mix I c t i).2.2 := by
      funext i; by_cases hi : i ∈ I <;> simp [mix, hi, c]
    beta_reduce
    rw [e1, e2, e3]
  have hmass := mass μ hμ.2 I c
  have hlow : α ^ I.card ≤ ∏ i ∈ I, μ (c i) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => hα0) fun i _ => hαμ (v i)
  have hH0 : ∀ u, 0 ≤ ∑ x, tensorPow μ n x * G (mix I u x) := fun u =>
    Finset.sum_nonneg fun x _ => mul_nonneg (tensorPow_nonneg μ hμ.1 x) (hG0 _)
  have key := sum_ge_of_const (tensorPow μ n) (fun u => ∑ x, tensorPow μ n x * G (mix I u x))
    (tensorPow_nonneg μ hμ.1) hH0 (fun u => ∀ i ∈ I, u i = c i)
    (∑ x, tensorPow μ n x * G (mix I c x)) (fun u hu => Finset.sum_congr rfl fun x _ => by rw [mix_eq_of_agree I u c x hu])
  rw [hmass, total μ hμ.2 I G] at key
  rw [hDf, hDr]
  calc α ^ I.card * ∑ x, tensorPow μ n x * G (mix I c x)
      ≤ (∏ i ∈ I, μ (c i)) * ∑ x, tensorPow μ n x * G (mix I c x) :=
        mul_le_mul_of_nonneg_right hlow (hH0 c)
    _ ≤ _ := key

/-- The iteration: either the current restriction is resilient, or a restriction with
density larger by `step` exists. -/
theorem iterate {n : ℕ} (ν : Sig → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hν1 : ∑ a, ν a = 1) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hαν : ∀ a, α ≤ ν a) (B : ℕ) (f : (Fin n → Sig) → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1)
    (δ : ℝ) (hδ : 0 < δ) (step : ℝ) (hstep : step = δ * α ^ B / 2) (hstep0 : 0 < step) :
    ∀ N : ℕ, ∀ (j : ℕ) (I : Finset (Fin n)) (v : Fin n → Sig),
      δ + j * step ≤ expect (tensorPow ν n) (fun x => f (mix I v x)) → I.card ≤ j * B →
      (1 - δ) / step < j + N →
      ∃ (I : Finset (Fin n)) (v : Fin n → Sig) (j : ℕ),
        Resilient ν B (1 / 2) (fun x => f (mix I v x)) ∧
        δ + j * step ≤ expect (tensorPow ν n) (fun x => f (mix I v x)) ∧ I.card ≤ j * B := by
  intro N
  induction N with
  | zero =>
    intro j I v hd _ hN
    exfalso
    have h1 := expect_le_one ν hν hν1 (fun x => f (mix I v x)) (fun x => hf _)
    have h2 : (j : ℝ) ≤ (1 - δ) / step := by
      rw [le_div_iff₀ hstep0]; linarith
    push_cast at hN
    linarith
  | succ N ih =>
    intro j I v hd hcard hN
    by_cases hres : Resilient ν B (1 / 2) (fun x => f (mix I v x))
    · exact ⟨I, v, j, hres, hd, hcard⟩
    simp only [Resilient, not_forall, not_le] at hres
    obtain ⟨I', hI', w, hw⟩ := hres
    set d := expect (tensorPow ν n) (fun x => f (mix I v x)) with hddef
    have hsmall : expect (tensorPow ν n) (fun x => f (mix I v (mix I' w x))) < d / 2 := by
      have : expect (tensorPow ν n) (fun x => f (mix I v (mix I' w x))) < 1 / 2 * d := hw
      linarith
    have hjs : 0 ≤ (j : ℝ) * step := mul_nonneg (Nat.cast_nonneg j) hstep0.le
    have hdδ : δ ≤ d := by linarith
    have hpow : α ^ B ≤ ∏ i ∈ I', ν (w i) :=
      (pow_le_pow_of_le_one hα0 hα1 hI').trans (by
        rw [← Finset.prod_const]
        exact Finset.prod_le_prod (fun _ _ => hα0) fun i _ => hαν (w i))
    have hαB : 0 < α ^ B := by
      have : 0 < δ * α ^ B := by linarith
      exact pos_of_mul_pos_right this hδ.le
    have hP0 : 0 < ∏ i ∈ I', ν (w i) := hαB.trans_le hpow
    obtain ⟨u, hu⟩ := increment (tensorPow ν n)
      (fun u => expect (tensorPow ν n) (fun x => f (mix I v (mix I' u x))))
      (tensorPow_nonneg ν hν) (sum_tensorPow ν hν1) (fun u => ∀ i ∈ I', u i = w i) w
      (fun u hu => by
        unfold expect
        exact Finset.sum_congr rfl fun x _ => by beta_reduce; rw [mix_eq_of_agree I' u w x hu])
      (∏ i ∈ I', ν (w i)) (mass ν hν1 I' w) hP0 d
      (by unfold expect; exact (total ν hν1 I' (fun y => f (mix I v y))).symm)
      (by linarith) hsmall
    simp only [mix_mix] at hu
    have hinc : δ + ((j + 1 : ℕ) : ℝ) * step ≤
        expect (tensorPow ν n) (fun x => f (mix (I ∪ I') (mix I v u) x)) := by
      refine le_trans ?_ hu
      have : δ * α ^ B ≤ d * ∏ i ∈ I', ν (w i) :=
        mul_le_mul hdδ hpow hαB.le (hδ.le.trans hdδ)
      push_cast
      rw [hstep] at hd ⊢
      nlinarith
    have hcard' : (I ∪ I').card ≤ (j + 1) * B := by
      have := Finset.card_union_le I I'
      rw [add_mul, one_mul]; omega
    refine ih (j + 1) (I ∪ I') (mix I v u) hinc hcard' ?_
    push_cast at hN ⊢
    linarith

end Setting

end RestrictedAP.Counting.Dev.C514

namespace RestrictedAP.Counting
open RestrictedAP.Counting.Dev.C514 in
theorem chk_claim_5_14_monotone (Sig : Type) [Fintype Sig] [DecidableEq Sig]
    (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ) (hμ : IsDist μ)
    (hmarg : ∀ i : Fin 3, marginal μ i = ν) (hdiag : ∀ x : Sig, μ (x, x, x) ≠ 0)
    (hemb : ¬ DistHasEmbedding ℤ μ) (α : ℝ) (hα : IsMinAtom μ α)
    (n B : ℕ) (δ' : ℕ → ℝ → ℝ)
    (hyp : ∀ (η : ℝ) (g : (Fin n → Sig) → ℝ), (∀ x, g x = 0 ∨ g x = 1) →
      Resilient ν B (1 / 2) g → η ≤ expect (tensorPow ν n) g → δ' B η ≤ Delta1 μ g)
    (f : (Fin n → Sig) → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hδ : 0 < expect (tensorPow ν n) f) :
    α ^ (2 * (B : ℝ) / (expect (tensorPow ν n) f * α ^ B)) *
        δ' B (expect (tensorPow ν n) f) ≤ Delta1 μ f := by
  obtain ⟨hα0, hαat, ⟨t0, ht0⟩⟩ := hα
  have hαμ : ∀ x, α ≤ μ (x, x, x) := fun x => hαat _ (hdiag x)
  have hαν : ∀ a, α ≤ ν a := fun a => (hαμ a).trans (nu_ge μ ν hμ hmarg a)
  have hν : ∀ a, 0 ≤ ν a := fun a => hα0.le.trans (hαν a)
  have hν1 := nu_sum μ ν hμ hmarg
  have hα1 : α ≤ 1 := by
    rw [← ht0, ← hμ.2]
    exact Finset.single_le_sum (fun x _ => hμ.1 x) (Finset.mem_univ t0)
  set δ := expect (tensorPow ν n) f with hδdef
  have hαB : 0 < α ^ B := pow_pos hα0 B
  set step := δ * α ^ B / 2 with hstep
  have hstep0 : 0 < step := by positivity
  let v0 : Fin n → Sig := fun _ => t0.1
  have hstart : δ + ((0 : ℕ) : ℝ) * step ≤
      expect (tensorPow ν n) (fun x => f (mix ∅ v0 x)) := by
    simp only [mix_empty, Nat.cast_zero, zero_mul, add_zero]; exact le_rfl
  obtain ⟨I, v, j, hres, hd, hcard⟩ := iterate ν hν hν1 α hα0.le hα1 hαν B f hf δ hδ step hstep
    hstep0 (⌊(1 - δ) / step⌋₊ + 1) 0 ∅ v0 hstart (by simp)
    (by push_cast; linarith [Nat.lt_floor_add_one ((1 - δ) / step)])
  have hg01 : ∀ x, f (mix I v x) = 0 ∨ f (mix I v x) = 1 := fun x => hf _
  have hjs : 0 ≤ (j : ℝ) * step := mul_nonneg (Nat.cast_nonneg j) hstep0.le
  have hgδ : δ ≤ expect (tensorPow ν n) (fun x => f (mix I v x)) := by linarith
  have hle1 := expect_le_one ν hν hν1 (fun x => f (mix I v x)) hg01
  have hH := hyp δ (fun x => f (mix I v x)) hg01 hres hgδ
  have hR := delta1_restrict μ hμ α hα0.le hαμ I v f hf
  have hDf0 := Delta1_nonneg μ hμ.1 f hf
  by_cases hneg : δ' B δ ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hα0.le _) hneg).trans hDf0
  push_neg at hneg
  have hk : ((I.card : ℕ) : ℝ) ≤ 2 * (B : ℝ) / (δ * α ^ B) := by
    have h1 : ((I.card : ℕ) : ℝ) ≤ (j : ℝ) * B := by exact_mod_cast hcard
    have h2 : (j : ℝ) * (δ * α ^ B) ≤ 2 := by
      have : (j : ℝ) * step ≤ 1 := by linarith
      rw [hstep] at this; linarith
    rw [le_div_iff₀ (by positivity)]
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    nlinarith [mul_le_mul_of_nonneg_left h2 hB0]
  have hpow : α ^ (2 * (B : ℝ) / (δ * α ^ B)) ≤ α ^ I.card := by
    rw [← Real.rpow_natCast α I.card]
    exact Real.rpow_le_rpow_of_exponent_ge hα0 hα1 hk
  calc α ^ (2 * (B : ℝ) / (δ * α ^ B)) * δ' B δ ≤ α ^ I.card * δ' B δ :=
        mul_le_mul_of_nonneg_right hpow hneg.le
    _ ≤ α ^ I.card * Delta1 μ (fun x => f (mix I v x)) :=
        mul_le_mul_of_nonneg_left hH (pow_nonneg hα0.le _)
    _ ≤ Delta1 μ f := hR

end RestrictedAP.Counting
end

theorem solution : type_of% @RestrictedAP.Counting.chk_claim_5_14_monotone := @RestrictedAP.Counting.chk_claim_5_14_monotone
