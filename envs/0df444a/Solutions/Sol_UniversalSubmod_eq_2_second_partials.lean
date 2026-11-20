-- Prove2me | solution 1 for UniversalSubmod.eq_2_second_partials
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:47:07.023285+00:00
-- url     : https://prove2.me/submissions/7191170e-bdf8-40a9-a0f3-795771205dff

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Eq2

open NonmonotoneSubmod.Shared

variable {n : ℕ}

/-- weight of `A` in the product measure restricted to the index set `U` -/
def wt (U : Finset (Fin n)) (y : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  ∏ l ∈ U, if l ∈ A then y l else 1 - y l

/-- expectation of `g` over subsets of `U` -/
def M (U : Finset (Fin n)) (g : Finset (Fin n) → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ A ∈ U.powerset, wt U y A * g A

lemma F_eq_M (f : Finset (Fin n) → ℝ) (y : Fin n → ℝ) : F f y = M Finset.univ f y := by
  unfold F M wt
  rw [Finset.powerset_univ]
  exact Finset.sum_congr rfl (fun A _ => mul_comm _ _)

lemma M_diff (U : Finset (Fin n)) (g : Finset (Fin n) → ℝ) : Differentiable ℝ (M U g) := by
  unfold M wt
  refine Differentiable.fun_sum (fun A _ => ?_)
  refine Differentiable.mul_const ?_ _
  have : ∀ l, Differentiable ℝ (fun y : Fin n → ℝ => if l ∈ A then y l else 1 - y l) := by
    intro l; by_cases h : l ∈ A <;> simp [h] <;> fun_prop
  fun_prop

lemma wt_insert_not (s : Finset (Fin n)) (i : Fin n) (hi : i ∉ s) (y : Fin n → ℝ)
    (t : Finset (Fin n)) (ht : t ⊆ s) : wt (insert i s) y t = (1 - y i) * wt s y t := by
  have : i ∉ t := fun h => hi (ht h)
  unfold wt
  rw [Finset.prod_insert hi]
  simp [this]

lemma wt_insert_mem (s : Finset (Fin n)) (i : Fin n) (hi : i ∉ s) (y : Fin n → ℝ)
    (t : Finset (Fin n)) : wt (insert i s) y (insert i t) = y i * wt s y t := by
  unfold wt
  rw [Finset.prod_insert hi]
  simp only [Finset.mem_insert, true_or, if_true]
  congr 1
  refine Finset.prod_congr rfl (fun l hl => ?_)
  have : l ≠ i := fun h => hi (h ▸ hl)
  simp [this]

lemma M_split (s : Finset (Fin n)) (i : Fin n) (hi : i ∉ s) (g : Finset (Fin n) → ℝ)
    (y : Fin n → ℝ) :
    M (insert i s) g y = (1 - y i) * M s g y + y i * M s (fun A => g (insert i A)) y := by
  unfold M
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [wt_insert_not s i hi y t (Finset.mem_powerset.mp ht)]; ring
  · refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [wt_insert_mem s i hi y t]; ring

lemma M_one (s : Finset (Fin n)) (y : Fin n → ℝ) : M s (fun _ => 1) y = 1 := by
  induction s using Finset.induction_on with
  | empty => simp [M, wt]
  | insert i s hi ih =>
    rw [M_split s i hi, ih]; ring

lemma M_add_single (s : Finset (Fin n)) (i : Fin n) (hi : i ∉ s) (g : Finset (Fin n) → ℝ)
    (y : Fin n → ℝ) (t : ℝ) : M s g (y + t • Pi.single i (1 : ℝ)) = M s g y := by
  unfold M
  refine Finset.sum_congr rfl (fun A _ => ?_)
  congr 1
  unfold wt
  refine Finset.prod_congr rfl (fun l hl => ?_)
  have : l ≠ i := fun h => hi (h ▸ hl)
  simp [this]

lemma M_sub (U : Finset (Fin n)) (g h : Finset (Fin n) → ℝ) (y : Fin n → ℝ) :
    M U g y - M U h y = M U (fun A => g A - h A) y := by
  unfold M
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun A _ => by ring)

/-- derivative along a line, in terms of `fderiv` -/
lemma fderiv_of_line {G : (Fin n → ℝ) → ℝ} (hG : Differentiable ℝ G) (y v : Fin n → ℝ) (D : ℝ)
    (h : HasDerivAt (fun t : ℝ => G (y + t • v)) D 0) : fderiv ℝ G y v = D := by
  have h1 : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have h2 := (hG (y + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 : fderiv ℝ G y v = D := by
    have := h2.unique h
    simpa using this
  exact h3

lemma line_deriv (s : Finset (Fin n)) (i : Fin n) (hi : i ∉ s) (g : Finset (Fin n) → ℝ)
    (y : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => M (insert i s) g (y + t • Pi.single i (1 : ℝ)))
      (M s (fun A => g (insert i A) - g A) y) 0 := by
  have e : ∀ t : ℝ, M (insert i s) g (y + t • Pi.single i (1 : ℝ)) =
      M s g y + (y i + t) * M s (fun A => g (insert i A) - g A) y := by
    intro t
    rw [M_split s i hi, M_add_single s i hi, M_add_single s i hi, ← M_sub]
    simp
    ring
  simp_rw [e]
  have := (((hasDerivAt_id (0 : ℝ)).const_add (y i)).mul_const
    (M s (fun A => g (insert i A) - g A) y)).const_add (M s g y)
  simpa using this

lemma fderiv_F_single (f : Finset (Fin n) → ℝ) (j : Fin n) (y : Fin n → ℝ) :
    fderiv ℝ (F f) y (Pi.single j (1 : ℝ)) =
      M (Finset.univ.erase j) (fun A => f (insert j A) - f A) y := by
  have hF : Differentiable ℝ (F f) := by
    have : F f = M Finset.univ f := funext (F_eq_M f)
    rw [this]; exact M_diff _ _
  apply fderiv_of_line hF
  have hu : (Finset.univ : Finset (Fin n)) = insert j (Finset.univ.erase j) := by simp
  have := line_deriv (Finset.univ.erase j) j (by simp) f y
  rw [← hu] at this
  simpa [F_eq_M] using this


lemma sets_eq1 (A : Finset (Fin n)) (i j : Fin n) : A ∪ {i, j} = insert j (insert i A) := by
  ext; simp; tauto

lemma sets_eq2 (A : Finset (Fin n)) (i : Fin n) : A ∪ {i} = insert i A := by
  ext; simp

lemma second_formula (f : Finset (Fin n) → ℝ) (x : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    fderiv ℝ (fun y => fderiv ℝ (F f) y (Pi.single j (1 : ℝ))) x (Pi.single i (1 : ℝ)) =
      M (Finset.univ \ {i, j}) (fun A => f (A ∪ {i, j}) - f (A ∪ {i}) - f (A ∪ {j}) + f A) x := by
  have e1 : (fun y => fderiv ℝ (F f) y (Pi.single j (1 : ℝ))) =
      M (Finset.univ.erase j) (fun A => f (insert j A) - f A) := funext (fderiv_F_single f j)
  rw [e1]
  have hs : Finset.univ.erase j = insert i (Finset.univ \ {i, j}) := by
    ext l; simp
    by_cases h : l = i <;> simp [h, hij]
  have hi : i ∉ (Finset.univ \ {i, j}) := by simp
  apply fderiv_of_line (M_diff _ _)
  rw [hs]
  have := line_deriv (Finset.univ \ {i, j}) i hi (fun A => f (insert j A) - f A) x
  refine this.congr_deriv ?_
  unfold M
  refine Finset.sum_congr rfl (fun A hA => ?_)
  have hiA : i ∉ A := fun h => hi (Finset.mem_powerset.mp hA h)
  have hjA : j ∉ A := fun h => by simpa using Finset.mem_powerset.mp hA h
  beta_reduce
  rw [sets_eq1, sets_eq2, sets_eq2]
  ring

end UniversalSubmod.Dev.Eq2

namespace UniversalSubmod

open NonmonotoneSubmod.Shared

theorem chk_eq_2_second_partials {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) (i j : Fin n) :
    let d2 : ℝ := fderiv ℝ (fun y => fderiv ℝ (F f) y (Pi.single j (1 : ℝ))) x (Pi.single i (1 : ℝ))
    (i ≠ j → d2 = ∑ A ∈ (Finset.univ \ {i, j}).powerset,
        (∏ l ∈ Finset.univ \ {i, j}, if l ∈ A then x l else 1 - x l) *
          (f (A ∪ {i, j}) - f (A ∪ {i}) - f (A ∪ {j}) + f A)) ∧
    (i = j → d2 = 0) ∧ d2 ≤ 0 ∧ |d2| ≤ 2 * OPT f := by
  intro d2
  have hOPT : ∀ S, f S ≤ OPT f := fun S => Finset.le_sup' f (Finset.mem_univ S)
  have hOPT0 : 0 ≤ OPT f := le_trans (hf0 ∅) (hOPT ∅)
  have hzero : i = j → d2 = 0 := by
    rintro rfl
    have e1 : (fun y => fderiv ℝ (F f) y (Pi.single i (1 : ℝ))) =
        Dev.Eq2.M (Finset.univ.erase i) (fun A => f (insert i A) - f A) :=
      funext (Dev.Eq2.fderiv_F_single f i)
    show fderiv ℝ (fun y => fderiv ℝ (F f) y (Pi.single i (1 : ℝ))) x (Pi.single i (1 : ℝ)) = 0
    rw [e1]
    apply Dev.Eq2.fderiv_of_line (Dev.Eq2.M_diff _ _)
    have : (fun t : ℝ => Dev.Eq2.M (Finset.univ.erase i) (fun A => f (insert i A) - f A)
        (x + t • Pi.single i (1 : ℝ))) = fun _ => Dev.Eq2.M (Finset.univ.erase i)
          (fun A => f (insert i A) - f A) x :=
      funext (fun t => Dev.Eq2.M_add_single _ i (by simp) _ _ _)
    rw [this]
    exact hasDerivAt_const _ _
  refine ⟨fun hij => ?_, hzero, ?_⟩
  · have := Dev.Eq2.second_formula f x i j hij
    exact this
  · by_cases hij : i = j
    · have := hzero hij
      refine ⟨by rw [this], by rw [this]; simpa using hOPT0⟩
    · have key : ∀ A ∈ (Finset.univ \ {i, j}).powerset,
          f (A ∪ {i, j}) - f (A ∪ {i}) - f (A ∪ {j}) + f A ≤ 0 ∧
          -(2 * OPT f) ≤ f (A ∪ {i, j}) - f (A ∪ {i}) - f (A ∪ {j}) + f A := by
        intro A hA
        have hiA : i ∉ A := fun h => by simpa using Finset.mem_powerset.mp hA h
        have hjA : j ∉ A := fun h => by simpa using Finset.mem_powerset.mp hA h
        refine ⟨?_, ?_⟩
        · have h := hf (A ∪ {i}) (A ∪ {j})
          have h1 : (A ∪ {i}) ∪ (A ∪ {j}) = A ∪ {i, j} := by ext; simp; tauto
          have h2 : (A ∪ {i}) ∩ (A ∪ {j}) = A := by
            ext l; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
            constructor
            · rintro ⟨h | h, h' | h'⟩
              · exact h
              · exact h
              · exact h'
              · exact absurd (h.symm.trans h') hij
            · intro h; exact ⟨Or.inl h, Or.inl h⟩
          rw [h1, h2] at h
          linarith
        · have := hOPT (A ∪ {i}); have := hOPT (A ∪ {j})
          have := hf0 (A ∪ {i, j}); have := hf0 A
          linarith
      have hform := Dev.Eq2.second_formula f x i j hij
      have hw : ∀ A, 0 ≤ Dev.Eq2.wt (Finset.univ \ {i, j}) x A := by
        intro A
        exact Finset.prod_nonneg (fun l _ => by
          split_ifs
          · exact (hx l).1
          · linarith [(hx l).2])
      have hsum1 : ∑ A ∈ (Finset.univ \ {i, j}).powerset, Dev.Eq2.wt (Finset.univ \ {i, j}) x A = 1 := by
        have := Dev.Eq2.M_one (Finset.univ \ {i, j}) x
        simpa [Dev.Eq2.M] using this
      have hd : d2 = ∑ A ∈ (Finset.univ \ {i, j}).powerset, Dev.Eq2.wt (Finset.univ \ {i, j}) x A *
          (f (A ∪ {i, j}) - f (A ∪ {i}) - f (A ∪ {j}) + f A) := hform
      have hle : d2 ≤ 0 := by
        rw [hd]
        exact Finset.sum_nonpos (fun A hA => mul_nonpos_of_nonneg_of_nonpos (hw A) (key A hA).1)
      refine ⟨hle, ?_⟩
      rw [abs_of_nonpos hle]
      have : -(2 * OPT f) ≤ d2 := by
        rw [hd]
        calc -(2 * OPT f) = ∑ A ∈ (Finset.univ \ {i, j}).powerset,
              Dev.Eq2.wt (Finset.univ \ {i, j}) x A * (-(2 * OPT f)) := by
              rw [← Finset.sum_mul, hsum1]; ring
          _ ≤ _ := Finset.sum_le_sum (fun A hA => mul_le_mul_of_nonneg_left (key A hA).2 (hw A))
      linarith

end UniversalSubmod
end

theorem solution : type_of% @UniversalSubmod.chk_eq_2_second_partials := @UniversalSubmod.chk_eq_2_second_partials
