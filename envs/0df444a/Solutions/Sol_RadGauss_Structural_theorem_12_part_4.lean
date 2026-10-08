-- Prove2me | solution 1 for RadGauss.Structural.theorem_12_part_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:55:36.552065+00:00
-- url     : https://prove2.me/submissions/259c7998-8e0f-4783-9f0d-f2b1e7b3b846

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity

open MeasureTheory
open scoped ENNReal Pointwise


namespace RadGauss.Structural

open RadGauss.RiskBound

lemma p4_sv_not (b : Bool) : signVal (!b) = - signVal b := by
  cases b <;> simp [signVal]

lemma p4_sv_cases (b : Bool) : signVal b = 1 ∨ signVal b = -1 := by
  cases b <;> simp [signVal]

/-- flip coordinate j -/
def p4_flip {n : ℕ} (j : Fin n) (σ : Fin n → Bool) : Fin n → Bool :=
  Function.update σ j (!σ j)

lemma p4_flip_invol {n : ℕ} (j : Fin n) : Function.Involutive (p4_flip j) := by
  intro σ
  funext i
  by_cases h : i = j
  · subst h; simp [p4_flip]
  · simp [p4_flip, Function.update_of_ne h]

/-- hybrid sum -/
noncomputable def p4_T {n : ℕ} {ι : Type*} (v : ι → Fin n → ℝ) (φ ψ : ℝ → ℝ)
    (J : Finset (Fin n)) (σ : Fin n → Bool) (k : ι) : ℝ :=
  ∑ i, signVal (σ i) * (if i ∈ J then ψ (v k i) else φ (v k i))

lemma p4_T_decomp {n : ℕ} {ι : Type*} (v : ι → Fin n → ℝ) (φ ψ : ℝ → ℝ)
    (J : Finset (Fin n)) (j : Fin n) (hj : j ∉ J) (σ : Fin n → Bool) (k : ι) :
    p4_T v φ ψ J σ k = signVal (σ j) * φ (v k j) +
      ∑ i ∈ Finset.univ.erase j, signVal (σ i) * (if i ∈ J then ψ (v k i) else φ (v k i)) ∧
    p4_T v φ ψ (insert j J) σ k = signVal (σ j) * ψ (v k j) +
      ∑ i ∈ Finset.univ.erase j, signVal (σ i) * (if i ∈ J then ψ (v k i) else φ (v k i)) ∧
    p4_T v φ ψ J (p4_flip j σ) k = - signVal (σ j) * φ (v k j) +
      ∑ i ∈ Finset.univ.erase j, signVal (σ i) * (if i ∈ J then ψ (v k i) else φ (v k i)) ∧
    p4_T v φ ψ (insert j J) (p4_flip j σ) k = - signVal (σ j) * ψ (v k j) +
      ∑ i ∈ Finset.univ.erase j, signVal (σ i) * (if i ∈ J then ψ (v k i) else φ (v k i)) := by
  unfold p4_T
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp [hj]
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [Finset.mem_insert, hij]
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    · simp [p4_flip, hj, p4_sv_not]
    · apply Finset.sum_congr rfl
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [p4_flip, Function.update_of_ne hij]
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    · simp [p4_flip, p4_sv_not]
    · apply Finset.sum_congr rfl
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [p4_flip, Function.update_of_ne hij, Finset.mem_insert, hij]

lemma p4_step {n : ℕ} {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (v : ι → Fin n → ℝ)
    (φ ψ : ℝ → ℝ) (h : ∀ a b, |φ a - φ b| ≤ |ψ a - ψ b|)
    (J : Finset (Fin n)) (j : Fin n) (hj : j ∉ J) (σ : Fin n → Bool) :
    s.sup' hs (p4_T v φ ψ J σ) + s.sup' hs (p4_T v φ ψ J (p4_flip j σ)) ≤
      s.sup' hs (p4_T v φ ψ (insert j J) σ) + s.sup' hs (p4_T v φ ψ (insert j J) (p4_flip j σ)) := by
  set RHS := s.sup' hs (p4_T v φ ψ (insert j J) σ) +
    s.sup' hs (p4_T v φ ψ (insert j J) (p4_flip j σ)) with hRHS
  have key : ∀ k ∈ s, ∀ w ∈ s, p4_T v φ ψ J σ k + p4_T v φ ψ J (p4_flip j σ) w ≤ RHS := by
    intro k hk w hw
    obtain ⟨a1, a2, a3, a4⟩ := p4_T_decomp v φ ψ J j hj σ k
    obtain ⟨b1, b2, b3, b4⟩ := p4_T_decomp v φ ψ J j hj σ w
    have hk1 := Finset.le_sup' (p4_T v φ ψ (insert j J) σ) hk
    have hk2 := Finset.le_sup' (p4_T v φ ψ (insert j J) (p4_flip j σ)) hk
    have hw1 := Finset.le_sup' (p4_T v φ ψ (insert j J) σ) hw
    have hw2 := Finset.le_sup' (p4_T v φ ψ (insert j J) (p4_flip j σ)) hw
    have hh := h (v k j) (v w j)
    rcases p4_sv_cases (σ j) with hs0 | hs0 <;>
    · rw [hs0] at a1 a2 a3 a4 b1 b2 b3 b4
      have e1 := le_abs_self (φ (v k j) - φ (v w j))
      have e2 := neg_abs_le (φ (v k j) - φ (v w j))
      rcases abs_cases (ψ (v k j) - ψ (v w j)) with ⟨hp, _⟩ | ⟨hp, _⟩ <;>
      · rw [hp] at hh
        first
          | linarith
  have hsum : s.sup' hs (p4_T v φ ψ J σ) ≤ RHS - s.sup' hs (p4_T v φ ψ J (p4_flip j σ)) := by
    apply Finset.sup'_le
    intro k hk
    have : s.sup' hs (p4_T v φ ψ J (p4_flip j σ)) ≤ RHS - p4_T v φ ψ J σ k := by
      apply Finset.sup'_le
      intro w hw
      have := key k hk w hw
      linarith
    linarith
  linarith

lemma p4_comp {n : ℕ} {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (v : ι → Fin n → ℝ)
    (φ ψ : ℝ → ℝ) (h : ∀ a b, |φ a - φ b| ≤ |ψ a - ψ b|) :
    ∑ σ : Fin n → Bool, s.sup' hs (fun k => ∑ i, signVal (σ i) * φ (v k i)) ≤
      ∑ σ : Fin n → Bool, s.sup' hs (fun k => ∑ i, signVal (σ i) * ψ (v k i)) := by
  have hJ : ∀ J : Finset (Fin n), ∑ σ : Fin n → Bool, s.sup' hs (p4_T v φ ψ ∅ σ) ≤
      ∑ σ : Fin n → Bool, s.sup' hs (p4_T v φ ψ J σ) := by
    intro J
    induction J using Finset.induction_on with
    | empty => exact le_rfl
    | insert j J hj ih =>
      refine ih.trans ?_
      have e : ∀ K : Finset (Fin n), ∑ σ : Fin n → Bool, s.sup' hs (p4_T v φ ψ K (p4_flip j σ)) =
          ∑ σ : Fin n → Bool, s.sup' hs (p4_T v φ ψ K σ) := fun K =>
        Equiv.sum_comp (p4_flip_invol j).toPerm (fun σ => s.sup' hs (p4_T v φ ψ K σ))
      have h2 : ∑ σ : Fin n → Bool, (s.sup' hs (p4_T v φ ψ J σ) + s.sup' hs (p4_T v φ ψ J (p4_flip j σ))) ≤
          ∑ σ : Fin n → Bool, (s.sup' hs (p4_T v φ ψ (insert j J) σ) +
            s.sup' hs (p4_T v φ ψ (insert j J) (p4_flip j σ))) :=
        Finset.sum_le_sum fun σ _ => p4_step s hs v φ ψ h J j hj σ
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e, e] at h2
      linarith
  have := hJ Finset.univ
  have e1 : ∀ σ, p4_T v φ ψ ∅ σ = fun k => ∑ i, signVal (σ i) * φ (v k i) := by
    intro σ; funext k; simp [p4_T]
  have e2 : ∀ σ, p4_T v φ ψ Finset.univ σ = fun k => ∑ i, signVal (σ i) * ψ (v k i) := by
    intro σ; funext k; simp [p4_T]
  simp only [e1, e2] at this
  exact this

lemma p4_sup'_mul {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    s.sup' hs (fun k => c * f k) = c * s.sup' hs f := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun k hk => mul_le_mul_of_nonneg_left (Finset.le_sup' f hk) hc
  · obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_sup' hs f
    rw [heq]
    exact Finset.le_sup' (fun k => c * f k) hk

lemma p4_main {n : ℕ} {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (v : ι → Fin n → ℝ)
    (φ : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hφ : ∀ a b, |φ a - φ b| ≤ L * |a - b|) (hφ0 : φ 0 = 0) :
    ∑ σ : Fin n → Bool, s.sup' hs (fun k => |∑ i, signVal (σ i) * φ (v k i)|) ≤
      2 * L * ∑ σ : Fin n → Bool, s.sup' hs (fun k => |∑ i, signVal (σ i) * v k i|) := by
  classical
  set s' : Finset (Option ι) := Finset.insertNone s
  have hs' : s'.Nonempty := ⟨none, by simp [s']⟩
  set v' : Option ι → Fin n → ℝ := fun o => o.elim 0 v
  let M : (Fin n → Bool) → ℝ := fun σ => s'.sup' hs' (fun o => ∑ i, signVal (σ i) * φ (v' o i))
  let N : (Fin n → Bool) → ℝ := fun σ => s'.sup' hs' (fun o => ∑ i, signVal (σ i) * (L * v' o i))
  let B : (Fin n → Bool) → ℝ := fun σ => s.sup' hs (fun k => |∑ i, signVal (σ i) * v k i|)
  have hnone : (none : Option ι) ∈ s' := by simp [s']
  have hsome : ∀ k ∈ s, (some k) ∈ s' := fun k hk => by simp [s', hk]
  have M0 : ∀ σ, 0 ≤ M σ := fun σ => by
    have := Finset.le_sup' (fun o => ∑ i, signVal (σ i) * φ (v' o i)) hnone
    simpa [v', hφ0] using this
  have hneg : Function.Involutive (fun (σ : Fin n → Bool) i => !σ i) := by
    intro σ; funext i; simp
  have step1 : ∀ σ, s.sup' hs (fun k => |∑ i, signVal (σ i) * φ (v k i)|) ≤
      M σ + M (fun i => !σ i) := by
    intro σ
    apply Finset.sup'_le
    intro k hk
    have h1 : ∑ i, signVal (σ i) * φ (v k i) ≤ M σ :=
      Finset.le_sup' (fun o => ∑ i, signVal (σ i) * φ (v' o i)) (hsome k hk)
    have h2 : ∑ i, signVal ((fun i => !σ i) i) * φ (v k i) ≤ M (fun i => !σ i) :=
      Finset.le_sup' (fun o => ∑ i, signVal ((fun i => !σ i) i) * φ (v' o i)) (hsome k hk)
    simp only [p4_sv_not, neg_mul, Finset.sum_neg_distrib] at h2
    have := M0 σ
    have := M0 (fun i => !σ i)
    rw [abs_le]
    constructor <;> linarith
  have step2 : ∑ σ : Fin n → Bool, M σ ≤ ∑ σ : Fin n → Bool, N σ := by
    apply p4_comp s' hs' v' φ (fun t => L * t)
    intro a b
    rw [← mul_sub, abs_mul, abs_of_nonneg hL]
    exact hφ a b
  have step3 : ∀ σ, N σ ≤ L * B σ := by
    intro σ
    obtain ⟨k0, hk0⟩ := hs
    have B0 : 0 ≤ B σ := (abs_nonneg _).trans (Finset.le_sup' (fun k => |∑ i, signVal (σ i) * v k i|) hk0)
    apply Finset.sup'_le
    intro o ho
    cases o with
    | none => simp [v']; positivity
    | some k =>
      have hk : k ∈ s := by simpa [s'] using ho
      have := Finset.le_sup' (fun k => |∑ i, signVal (σ i) * v k i|) hk
      simp only [v', Option.elim]
      have e : ∑ i, signVal (σ i) * (L * v k i) = L * ∑ i, signVal (σ i) * v k i := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans this) hL
  have eneg : ∑ σ : Fin n → Bool, M (fun i => !σ i) = ∑ σ : Fin n → Bool, M σ :=
    Equiv.sum_comp hneg.toPerm M
  calc ∑ σ : Fin n → Bool, s.sup' hs (fun k => |∑ i, signVal (σ i) * φ (v k i)|)
      ≤ ∑ σ : Fin n → Bool, (M σ + M (fun i => !σ i)) := Finset.sum_le_sum fun σ _ => step1 σ
    _ = 2 * ∑ σ : Fin n → Bool, M σ := by rw [Finset.sum_add_distrib, eneg]; ring
    _ ≤ 2 * ∑ σ : Fin n → Bool, N σ := by linarith
    _ ≤ 2 * ∑ σ : Fin n → Bool, L * B σ := by
        have := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => step3 σ
        linarith
    _ = 2 * L * ∑ σ : Fin n → Bool, B σ := by rw [← Finset.mul_sum]; ring

lemma p4_emp {X : Type*} (n : ℕ) (F : Set (X → ℝ)) (φ : ℝ → ℝ) (Lφ : NNReal)
    (hφ : LipschitzWith Lφ φ) (hφ0 : φ 0 = 0) (x : Fin n → X) :
    empiricalRademacher n ((fun f => φ ∘ f) '' F) x ≤
      2 * (Lφ : ℝ≥0∞) * empiricalRademacher n F x := by
  unfold empiricalRademacher
  set c : ℝ := 2 / (n : ℝ) with hcdef
  have hc : 0 ≤ c := by positivity
  rw [show 2 * (Lφ : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
      ⨆ g ∈ F, ENNReal.ofReal |c * ∑ i, signVal (σ i) * g (x i)|) =
      ((2 : ℝ≥0∞) ^ n)⁻¹ * (2 * (Lφ : ℝ≥0∞) * ∑ σ : Fin n → Bool,
      ⨆ g ∈ F, ENNReal.ofReal |c * ∑ i, signVal (σ i) * g (x i)|) by ring]
  gcongr ((2 : ℝ≥0∞) ^ n)⁻¹ * ?_
  rcases F.eq_empty_or_nonempty with hF | hF
  · subst hF; simp
  haveI : Nonempty F := hF.to_subtype
  have hlip : ∀ a b, |φ a - φ b| ≤ (Lφ : ℝ) * |a - b| := by
    intro a b
    have := hφ.dist_le_mul a b
    simpa [Real.dist_eq] using this
  let P : (Fin n → Bool) → F → ℝ≥0∞ := fun σ f =>
    ENNReal.ofReal (c * |∑ i, signVal (σ i) * φ ((f : X → ℝ) (x i))|)
  let Q : (Fin n → Bool) → F → ℝ≥0∞ := fun σ f =>
    ENNReal.ofReal (c * |∑ i, signVal (σ i) * (f : X → ℝ) (x i)|)
  have hl : ∀ σ : Fin n → Bool, (⨆ g ∈ (fun f => φ ∘ f) '' F,
      ENNReal.ofReal |c * ∑ i, signVal (σ i) * g (x i)|) = ⨆ G : (Fin n → Bool) → F, P σ (G σ) := by
    intro σ
    rw [iSup_image]
    apply le_antisymm
    · refine iSup₂_le fun f hf => ?_
      refine le_iSup_of_le (fun _ => ⟨f, hf⟩) ?_
      simp [P, abs_mul, abs_of_nonneg hc]
    · refine iSup_le fun G => ?_
      refine le_iSup₂_of_le (G σ : X → ℝ) (G σ).2 ?_
      simp [P, abs_mul, abs_of_nonneg hc]
  have hr : ∀ σ : Fin n → Bool, ∀ f : F, Q σ f ≤
      ⨆ g ∈ F, ENNReal.ofReal |c * ∑ i, signVal (σ i) * g (x i)| := by
    intro σ f
    refine le_iSup₂_of_le (f : X → ℝ) f.2 ?_
    simp [Q, abs_mul, abs_of_nonneg hc]
  simp_rw [hl]
  rw [ENNReal.finsetSum_iSup]
  swap
  · intro G1 G2
    refine ⟨fun σ => if P σ (G1 σ) ≤ P σ (G2 σ) then G2 σ else G1 σ, fun σ => ?_⟩
    by_cases h : P σ (G1 σ) ≤ P σ (G2 σ)
    · beta_reduce; rw [if_pos h]; exact ⟨h, le_rfl⟩
    · beta_reduce; rw [if_neg h]; exact ⟨le_rfl, (not_le.mp h).le⟩
  refine iSup_le fun G => ?_
  set v : (Fin n → Bool) → Fin n → ℝ := fun τ i => (G τ : X → ℝ) (x i)
  have hm := p4_main (Finset.univ : Finset (Fin n → Bool)) Finset.univ_nonempty v φ (Lφ : ℝ)
    Lφ.2 hlip hφ0
  set R := ∑ σ : Fin n → Bool, Finset.univ.sup' Finset.univ_nonempty
    (fun k => |∑ i, signVal (σ i) * φ (v k i)|)
  set R' := ∑ σ : Fin n → Bool, Finset.univ.sup' Finset.univ_nonempty
    (fun k => |∑ i, signVal (σ i) * v k i|)
  have hsupnn : ∀ σ : Fin n → Bool, 0 ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun k => |∑ i, signVal (σ i) * v k i|) := fun σ =>
    (abs_nonneg _).trans (Finset.le_sup' (fun k => |∑ i, signVal (σ i) * v k i|) (Finset.mem_univ σ))
  have hsupnn' : ∀ σ : Fin n → Bool, 0 ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun k => |∑ i, signVal (σ i) * φ (v k i)|) := fun σ =>
    (abs_nonneg _).trans (Finset.le_sup' (fun k => |∑ i, signVal (σ i) * φ (v k i)|) (Finset.mem_univ σ))
  calc ∑ σ : Fin n → Bool, P σ (G σ)
      ≤ ∑ σ : Fin n → Bool, ENNReal.ofReal (c * Finset.univ.sup' Finset.univ_nonempty
          (fun k => |∑ i, signVal (σ i) * φ (v k i)|)) := by
        apply Finset.sum_le_sum
        intro σ _
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ hc
        exact Finset.le_sup' (fun k => |∑ i, signVal (σ i) * φ (v k i)|) (Finset.mem_univ σ)
    _ = ENNReal.ofReal (c * R) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun σ _ => mul_nonneg hc (hsupnn' σ)), Finset.mul_sum]
    _ ≤ ENNReal.ofReal (2 * (Lφ : ℝ) * (c * R')) := by
        apply ENNReal.ofReal_le_ofReal
        have := mul_le_mul_of_nonneg_left hm hc
        linarith
    _ = 2 * (Lφ : ℝ≥0∞) * ∑ σ : Fin n → Bool, ENNReal.ofReal (c * Finset.univ.sup' Finset.univ_nonempty
          (fun k => |∑ i, signVal (σ i) * v k i|)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_coe_nnreal, Finset.mul_sum,
          ENNReal.ofReal_sum_of_nonneg (fun σ _ => mul_nonneg hc (hsupnn σ))]
        norm_num
    _ ≤ 2 * (Lφ : ℝ≥0∞) * ∑ σ : Fin n → Bool,
          ⨆ g ∈ F, ENNReal.ofReal |c * ∑ i, signVal (σ i) * g (x i)| := by
        gcongr with σ _
        obtain ⟨τ, -, hτ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
          (fun k => |∑ i, signVal (σ i) * v k i|)
        rw [hτ]
        exact hr σ (G τ)

theorem p4_core {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F : Set (X → ℝ)) (φ : ℝ → ℝ) (Lφ : NNReal)
    (hφ : LipschitzWith Lφ φ) (hφ0 : φ 0 = 0) :
    RadGauss.RiskBound.rademacherComplexity μ n ((fun f => φ ∘ f) '' F) ≤
      2 * (Lφ : ℝ≥0∞) * RadGauss.RiskBound.rademacherComplexity μ n F := by
  unfold rademacherComplexity
  rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by simp) (by simp))]
  exact lintegral_mono fun x => p4_emp n F φ Lφ hφ hφ0 x

end RadGauss.Structural

open RadGauss.Structural


theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F : Set (X → ℝ)) (φ : ℝ → ℝ) (Lφ : NNReal)
    (hφ : LipschitzWith Lφ φ) (hφ0 : φ 0 = 0) :
    RadGauss.RiskBound.rademacherComplexity μ n ((fun f => φ ∘ f) '' F) ≤
      2 * (Lφ : ℝ≥0∞) * RadGauss.RiskBound.rademacherComplexity μ n F := by
  exact p4_core μ n F φ Lφ hφ hφ0
