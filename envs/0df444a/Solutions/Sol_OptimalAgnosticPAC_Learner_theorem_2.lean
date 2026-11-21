-- Prove2me | solution 1 for OptimalAgnosticPAC.Learner.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:16:09.809717+00:00
-- url     : https://prove2.me/submissions/a7db5d1e-73a2-45a0-9ab9-463c3432b1ce

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Cube
import Theorems.Thm_OptimalAgnosticPAC_Learner_lemma_2_1
import Theorems.Thm_OptimalAgnosticPAC_Learner_eq_4_rademacher_width
import Theorems.Thm_OptimalAgnosticPAC_Learner_hall_orientation
import Definitions.Def_OptimalAgnosticPAC_Learner_Risk

section
open scoped Classical
namespace OptimalAgnosticPAC.Dev.Cube
open OptimalAgnosticPAC.Learner

variable {P : Type} [Fintype P]

/-- ordered pairs (v,p) with both v and its p-neighbour in U -/
noncomputable def A (U : Finset (P → Bool)) : Finset ((P → Bool) × P) :=
  (U ×ˢ (Finset.univ : Finset P)).filter (fun z => flipAt z.1 z.2 ∈ U)

theorem sum_A (U : Finset (P → Bool)) (f : (P → Bool) × P → ℝ) :
    ∑ v ∈ U, ∑ p ∈ dirs U v, f (v, p) = ∑ z ∈ A U, f z := by
  rw [A, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [dirs, Finset.sum_filter]

theorem sum_A_inv (U : Finset (P → Bool)) (f : (P → Bool) × P → ℝ) :
    ∑ z ∈ A U, f (flipAt z.1 z.2, z.2) = ∑ z ∈ A U, f z := by
  refine Finset.sum_nbij' (fun z => (flipAt z.1 z.2, z.2)) (fun z => (flipAt z.1 z.2, z.2))
    ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [A, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hz ⊢
    rw [flipAt_flipAt]; exact ⟨hz.2, hz.1⟩
  · intro z hz
    simp only [A, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hz ⊢
    rw [flipAt_flipAt]; exact ⟨hz.2, hz.1⟩
  · intro z _; simp [flipAt_flipAt]
  · intro z _; simp [flipAt_flipAt]
  · intro z _; rfl

theorem two_edges_le (U : Finset (P → Bool)) :
    2 * (inducedEdges (cubeGraph P) U).card ≤ (A U).card := by
  let g : (P → Bool) × P → Sym2 (P → Bool) := fun z => s(z.1, flipAt z.1 z.2)
  have hsub : inducedEdges (cubeGraph P) U ⊆ (A U).image g := by
    intro e he
    simp only [inducedEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨he1, he2⟩ := he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet] at he1
      obtain ⟨p, hp⟩ := he1
      have hu := he2 u (by simp)
      have hv := he2 v (by simp)
      simp only [Finset.mem_image, A, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        and_true]
      refine ⟨(u, p), ⟨hu, by rw [← hp]; exact hv⟩, ?_⟩
      simp [g, hp]
  have h2 : 2 * ((A U).image g).card ≤ (A U).card := by
    refine Finset.mul_card_image_le_card (f := g) (A U) 2 ?_
    intro e he
    simp only [Finset.mem_image] at he
    obtain ⟨z, hz, rfl⟩ := he
    have hz' := hz
    simp only [A, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hz'
    have h1 : z ∈ (A U).filter (fun x => g x = g z) := by simp [hz]
    have h2 : (flipAt z.1 z.2, z.2) ∈ (A U).filter (fun x => g x = g z) := by
      simp only [Finset.mem_filter, A, Finset.mem_product, Finset.mem_univ, and_true]
      refine ⟨⟨hz'.2, ?_⟩, ?_⟩
      · rw [flipAt_flipAt]; exact hz'.1
      · simp only [g, flipAt_flipAt]; exact Sym2.eq_swap
    have hne : z ≠ (flipAt z.1 z.2, z.2) := by
      intro h; exact flipAt_ne z.1 z.2 (congrArg Prod.fst h)
    exact Finset.one_lt_card.2 ⟨z, h1, _, h2, hne⟩
  have := Finset.card_le_card hsub
  omega

/-- the double count: edges ≤ sum of weights, when w v p + w (flip v p) p = 1 -/
theorem edges_le_sum_w (U : Finset (P → Bool)) (w : (P → Bool) → P → ℝ)
    (hw : ∀ v p, w v p + w (flipAt v p) p = 1) :
    ((inducedEdges (cubeGraph P) U).card : ℝ) ≤ ∑ v ∈ U, ∑ p ∈ dirs U v, w v p := by
  have h1 : ∑ z ∈ A U, (w z.1 z.2 + w (flipAt z.1 z.2) z.2) = (A U).card := by
    rw [Finset.sum_congr rfl (fun z _ => hw z.1 z.2)]; simp
  have h2 : ∑ z ∈ A U, w (flipAt z.1 z.2) z.2 = ∑ z ∈ A U, w z.1 z.2 :=
    sum_A_inv U (fun z => w z.1 z.2)
  rw [Finset.sum_add_distrib, h2] at h1
  have h3 := sum_A U (fun z => w z.1 z.2)
  have h4 : (2 * (inducedEdges (cubeGraph P) U).card : ℝ) ≤ (A U).card := by
    exact_mod_cast two_edges_le U
  simp only at h3
  linarith
end OptimalAgnosticPAC.Dev.Cube
end

section
open scoped Classical
namespace OptimalAgnosticPAC.Dev.Ineq
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.Cube

/-- the pairwise inequality, linear in w -/
theorem pair_ineq (d : ℝ) (hd : 1 ≤ d) (b b' w w' : ℝ) (hb : 0 < b) (hb' : 0 < b')
    (hbd : 3601 * d ≤ b ^ 2) (hbd' : 3601 * d ≤ b' ^ 2) (hbb : |b ^ 2 - b' ^ 2| ≤ 1)
    (hw : 0 ≤ w) (hw' : 0 ≤ w') (hww : w + w' = 1) :
    1 / b + 1 / b' ≤ (2 + 1 / (7202 * d)) * (w / b + w' / b') := by
  set ε : ℝ := 1 / (7202 * d) with hε
  have hε0 : 0 ≤ ε := by positivity
  have h2ε : 2 * ε = 1 / (3601 * d) := by rw [hε]; field_simp; ring
  have hsq : ∀ x y : ℝ, 0 < x → 0 < y → 3601 * d ≤ x ^ 2 → y ^ 2 - x ^ 2 ≤ 1 → y ≤ (1 + ε) * x := by
    intro x y hx hy hxd hxy
    apply le_of_sq_le_sq _ (by positivity)
    have h1 : y ^ 2 ≤ x ^ 2 + 1 := by linarith
    have h3 : 1 ≤ x ^ 2 * (2 * ε) := by
      rw [h2ε]; rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
    nlinarith [sq_nonneg (ε * x)]
  have h1 := hsq b b' hb hb' hbd (by linarith [(abs_le.1 hbb).1])
  have h2 := hsq b' b hb' hb hbd' (by linarith [(abs_le.1 hbb).2])
  have e1 : (1 + ε) / b - 1 / b' ≥ 0 := by
    rw [ge_iff_le, sub_nonneg, div_le_div_iff₀ hb' hb]; nlinarith
  have e2 : (1 + ε) / b' - 1 / b ≥ 0 := by
    rw [ge_iff_le, sub_nonneg, div_le_div_iff₀ hb hb']; nlinarith
  have : (2 + ε) * (w / b + w' / b') - (1 / b + 1 / b') =
      w * ((1 + ε) / b - 1 / b') + w' * ((1 + ε) / b' - 1 / b) := by
    have : w' = 1 - w := by linarith
    subst this; ring
  nlinarith [mul_nonneg hw e1, mul_nonneg hw' e2]

variable {P : Type} [Fintype P]

theorem main_ineq (d : ℕ) (hd : 1 ≤ d) (U : Finset (P → Bool)) (ρ : (P → Bool) → ℝ)
    (hρ0 : ∀ v, 0 ≤ ρ v) (hρ1 : ∀ v p, |ρ v - ρ (flipAt v p)| ≤ 1)
    (w : (P → Bool) → P → ℝ) (hw0 : ∀ v p, 0 ≤ w v p) (hw : ∀ v p, w v p + w (flipAt v p) p = 1)
    (hs : ∀ v, ∑ p ∈ dirs U v, w v p ≤ ρ v + 60 * Real.sqrt (d * (dirs U v).card)) :
    ∑ v ∈ U, ∑ p ∈ dirs U v, w v p ≤
      ∑ v ∈ U, (ρ v + 120 * Real.sqrt (d * (ρ v + 3601 * d))) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set b : (P → Bool) → ℝ := fun v => Real.sqrt (ρ v + 3601 * d) with hbdef
  have hbsq : ∀ v, b v ^ 2 = ρ v + 3601 * d := fun v => by
    rw [hbdef]; exact Real.sq_sqrt (by have := hρ0 v; positivity)
  have hbpos : ∀ v, 0 < b v := fun v => Real.sqrt_pos.2 (by have := hρ0 v; positivity)
  set ε : ℝ := 1 / (7202 * (d : ℝ)) with hε
  set deg : (P → Bool) → ℝ := fun v => ((dirs U v).card : ℝ) with hdeg
  set s : (P → Bool) → ℝ := fun v => ∑ p ∈ dirs U v, w v p with hsdef
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 / 7202 := by
    rw [hε]; apply one_div_le_one_div_of_le (by norm_num); nlinarith
  -- F1
  have F1 : ∀ v, s v ≤ b v ^ 2 + 900 / 3601 * deg v := by
    intro v
    have h := hs v
    have h60 : 60 * Real.sqrt (d * (dirs U v).card) ≤ 3601 * d + 900 / 3601 * deg v := by
      have hr := Real.sq_sqrt (show 0 ≤ (d : ℝ) * (dirs U v).card by positivity)
      have hr0 := Real.sqrt_nonneg ((d : ℝ) * (dirs U v).card)
      have hc : deg v = ((dirs U v).card : ℝ) := rfl
      have hc0 : 0 ≤ deg v := by rw [hc]; positivity
      apply le_of_sq_le_sq _ (by positivity)
      nlinarith [sq_nonneg (3601 * (d : ℝ) - 900 / 3601 * deg v), hr]
    rw [hbsq]; linarith
  have hd0 : (0 : ℝ) ≤ d := by positivity
  -- double sums over A
  have hA1 : ∑ z ∈ A U, (1 / b z.1 + 1 / b (flipAt z.1 z.2)) = 2 * ∑ v ∈ U, deg v / b v := by
    rw [Finset.sum_add_distrib, sum_A_inv U (fun z => 1 / b z.1)]
    have := sum_A U (fun z => 1 / b z.1)
    simp only at this
    have h2 : ∑ v ∈ U, ∑ p ∈ dirs U v, 1 / b v = ∑ v ∈ U, deg v / b v := by
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Finset.sum_const, nsmul_eq_mul, hdeg]; ring
    rw [h2] at this; rw [← this]; ring
  have hA2 : ∑ z ∈ A U, (w z.1 z.2 / b z.1 + w (flipAt z.1 z.2) z.2 / b (flipAt z.1 z.2)) =
      2 * ∑ v ∈ U, s v / b v := by
    rw [Finset.sum_add_distrib, sum_A_inv U (fun z => w z.1 z.2 / b z.1)]
    have := sum_A U (fun z => w z.1 z.2 / b z.1)
    simp only at this
    have h2 : ∑ v ∈ U, ∑ p ∈ dirs U v, w v p / b v = ∑ v ∈ U, s v / b v := by
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [hsdef, ← Finset.sum_div]
    rw [h2] at this; rw [← this]; ring
  have hpair : ∀ z ∈ A U, 1 / b z.1 + 1 / b (flipAt z.1 z.2) ≤
      (2 + ε) * (w z.1 z.2 / b z.1 + w (flipAt z.1 z.2) z.2 / b (flipAt z.1 z.2)) := by
    intro z _
    have hr := hρ0 z.1; have hr' := hρ0 (flipAt z.1 z.2)
    refine pair_ineq d hdR _ _ _ _ (hbpos _) (hbpos _) ?_ ?_ ?_ (hw0 _ _) (hw0 _ _) (hw _ _)
    · rw [hbsq]; linarith
    · rw [hbsq]; linarith
    · rw [hbsq, hbsq]; have := hρ1 z.1 z.2; convert this using 2; ring
  have hT : ∑ v ∈ U, deg v / b v ≤ (2 + ε) * ∑ v ∈ U, s v / b v := by
    have := Finset.sum_le_sum hpair
    rw [hA1, ← Finset.mul_sum, hA2] at this
    · linarith
  have hSs : ∑ v ∈ U, s v / b v ≤ ∑ v ∈ U, b v + 900 / 3601 * ∑ v ∈ U, deg v / b v := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun v _ => ?_)
    have := F1 v
    have hb := hbpos v
    rw [div_le_iff₀ hb]
    have : (b v + 900 / 3601 * (deg v / b v)) * b v = b v ^ 2 + 900 / 3601 * deg v := by
      field_simp
    linarith
  have hB0 : 0 ≤ ∑ v ∈ U, b v := Finset.sum_nonneg (fun v _ => (hbpos v).le)
  have hT0 : 0 ≤ ∑ v ∈ U, deg v / b v :=
    Finset.sum_nonneg (fun v _ => div_nonneg (by rw [hdeg]; positivity) (hbpos v).le)
  have hT4 : ∑ v ∈ U, deg v / b v ≤ 4 * ∑ v ∈ U, b v := by
    set T := ∑ v ∈ U, deg v / b v
    set B := ∑ v ∈ U, b v
    set Ss := ∑ v ∈ U, s v / b v
    have h1 : T ≤ (2 + ε) * (B + 900 / 3601 * T) :=
      hT.trans (mul_le_mul_of_nonneg_left hSs (by positivity))
    have h2 : ε * B ≤ B / 7202 := by nlinarith
    have h3 : ε * T ≤ T / 7202 := by nlinarith
    nlinarith
  have hrt : ∀ v, Real.sqrt (deg v) ≤ deg v / b v / 4 + b v := by
    intro v
    have hb := hbpos v
    have hc0 : 0 ≤ deg v := by rw [hdeg]; positivity
    have hr := Real.sq_sqrt hc0
    have : Real.sqrt (deg v) ≤ (Real.sqrt (deg v)) ^ 2 / (4 * b v) + b v := by
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (Real.sqrt (deg v) - 2 * b v)]
    rw [hr] at this
    calc _ ≤ _ := this
      _ = _ := by field_simp
  have hsq : ∑ v ∈ U, Real.sqrt (deg v) ≤ 2 * ∑ v ∈ U, b v := by
    calc _ ≤ ∑ v ∈ U, (deg v / b v / 4 + b v) := Finset.sum_le_sum (fun v _ => hrt v)
      _ = (∑ v ∈ U, deg v / b v) / 4 + ∑ v ∈ U, b v := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div]
      _ ≤ _ := by linarith
  have hfin : ∀ v, Real.sqrt (d * (dirs U v).card) = Real.sqrt d * Real.sqrt (deg v) := fun v => by
    rw [hdeg]; exact Real.sqrt_mul hd0 _
  have hbv : ∀ v, Real.sqrt (d * (ρ v + 3601 * d)) = Real.sqrt d * b v := fun v => by
    rw [hbdef]; exact Real.sqrt_mul hd0 _
  calc ∑ v ∈ U, ∑ p ∈ dirs U v, w v p ≤ ∑ v ∈ U, (ρ v + 60 * (Real.sqrt d * Real.sqrt (deg v))) :=
        Finset.sum_le_sum (fun v _ => by have := hs v; rw [hfin] at this; exact this)
    _ = ∑ v ∈ U, ρ v + 60 * Real.sqrt d * ∑ v ∈ U, Real.sqrt (deg v) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl (fun v _ => ?_); ring
    _ ≤ ∑ v ∈ U, ρ v + 60 * Real.sqrt d * (2 * ∑ v ∈ U, b v) := by
        gcongr
    _ = ∑ v ∈ U, (ρ v + 120 * Real.sqrt (d * (ρ v + 3601 * d))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [hbv]
        rw [← Finset.mul_sum]
        ring
end OptimalAgnosticPAC.Dev.Ineq
end

section
open scoped Classical
namespace OptimalAgnosticPAC.Dev.T2a
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.Cube OptimalAgnosticPAC.Dev.Ineq

variable {P : Type} [Fintype P]

theorem rho_le (F : Set (P → Bool)) (v : P → Bool) {f} (hf : f ∈ F) :
    rho F v ≤ (DIS v f).card := Nat.sInf_le ⟨f, hf, rfl⟩

theorem rho_attained (F : Set (P → Bool)) (hF : F.Nonempty) (v : P → Bool) :
    ∃ f ∈ F, rho F v = (DIS v f).card := by
  have := Nat.sInf_mem (s := (fun f => (DIS v f).card) '' F) (hF.image _)
  obtain ⟨f, hf, h⟩ := this
  exact ⟨f, hf, h.symm⟩

theorem dis_le (v : P → Bool) (p : P) (f : P → Bool) :
    (DIS v f).card ≤ (DIS (flipAt v p) f).card + 1 := by
  have : DIS v f ⊆ insert p (DIS (flipAt v p) f) := by
    intro r hr
    simp only [DIS, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    simp only [Finset.mem_insert, DIS, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : r = p
    · exact Or.inl h
    · right; simpa [flipAt, Function.update_of_ne h] using hr
  exact (Finset.card_le_card this).trans (Finset.card_insert_le _ _)

theorem rho_flip (F : Set (P → Bool)) (hF : F.Nonempty) (v : P → Bool) (p : P) :
    |(rho F v : ℝ) - rho F (flipAt v p)| ≤ 1 := by
  have key : ∀ v p, rho F v ≤ rho F (flipAt v p) + 1 := by
    intro v p
    obtain ⟨f, hf, h⟩ := rho_attained F hF (flipAt v p)
    exact (rho_le F v hf).trans (by have := dis_le v p f; omega)
  have h1 := key v p
  have h2 := key (flipAt v p) p
  rw [flipAt_flipAt] at h2
  rw [abs_le]; constructor <;> [skip; skip] <;> (have h1' : (rho F v : ℝ) ≤ rho F (flipAt v p) + 1 := by exact_mod_cast h1
                                                 have h2' : (rho F (flipAt v p) : ℝ) ≤ rho F v + 1 := by exact_mod_cast h2
                                                 linarith)

theorem sqrt_bound (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr : 0 ≤ r) :
    120 * Real.sqrt (d * (r + 3601 * d)) + 1 ≤ 120 * Real.sqrt (d * r) + 7202 * d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : Real.sqrt (d * (r + 3601 * d)) ≤ Real.sqrt (d * r) + Real.sqrt (3601) * d := by
    have : (d : ℝ) * (r + 3601 * d) = d * r + 3601 * d ^ 2 := by ring
    rw [this]
    have ha := Real.sq_sqrt (show 0 ≤ (d : ℝ) * r by positivity)
    have hb := Real.sq_sqrt (show (0 : ℝ) ≤ 3601 * d ^ 2 by positivity)
    have hb' : Real.sqrt (3601 * (d : ℝ) ^ 2) = Real.sqrt 3601 * d := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
    rw [← hb']
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sqrt_nonneg ((d : ℝ) * r), Real.sqrt_nonneg (3601 * (d : ℝ) ^ 2),
      mul_nonneg (Real.sqrt_nonneg ((d : ℝ) * r)) (Real.sqrt_nonneg (3601 * (d : ℝ) ^ 2))]
  have h2 : Real.sqrt 3601 ≤ 7201 / 120 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  nlinarith


theorem part1 (d : ℕ) (hd : 1 ≤ d) (P : Type) [Fintype P] [Nonempty P] (F : Set (P → Bool))
    (hF : F.Nonempty) (hVC : HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞)) :
    ∃ σ : Sym2 (P → Bool) → (P → Bool), IsOrientation (cubeGraph P) σ ∧
      ∀ v : P → Bool, (outdegree (cubeGraph P) σ v : ℝ) ≤
        (rho F v : ℝ) + 120 * Real.sqrt ((d : ℝ) * (rho F v : ℝ)) + 7202 * (d : ℝ) := by
  obtain ⟨w, hw01, hw5, hw6⟩ := (lemma_2_1 F hF).1
  have hU : ∀ U : Finset (P → Bool), ((inducedEdges (cubeGraph P) U).card : ℝ) ≤
      ∑ v ∈ U, ((rho F v : ℝ) + 120 * Real.sqrt ((d : ℝ) * ((rho F v : ℝ) + 3601 * d))) := by
    intro U
    refine (edges_le_sum_w U w hw5).trans (main_ineq d hd U (fun v => (rho F v : ℝ))
      (fun v => by positivity) (rho_flip F hF) w (fun v p => (hw01 v p).1) hw5 ?_)
    intro v
    have h1 := hw6 v (dirs U v)
    have h2 := eq_4_rademacher_width d hd F hF hVC (dirs U v)
    linarith
  let c : (P → Bool) → ℕ := fun v =>
    ⌈(rho F v : ℝ) + 120 * Real.sqrt ((d : ℝ) * ((rho F v : ℝ) + 3601 * d))⌉₊
  have hc : ∀ W : Finset (P → Bool), (inducedEdges (cubeGraph P) W).card ≤ ∑ x ∈ W, c x := by
    intro W
    have h := hU W
    have : ∑ v ∈ W, ((rho F v : ℝ) + 120 * Real.sqrt ((d : ℝ) * ((rho F v : ℝ) + 3601 * d))) ≤
        ((∑ x ∈ W, c x : ℕ) : ℝ) := by
      push_cast
      exact Finset.sum_le_sum (fun v _ => Nat.le_ceil _)
    exact_mod_cast h.trans this
  obtain ⟨_, σ, hσ, hout⟩ := hall_orientation (cubeGraph P) c hc
  refine ⟨σ, hσ, fun v => ?_⟩
  have h1 : (outdegree (cubeGraph P) σ v : ℝ) ≤ c v := by exact_mod_cast hout v
  have h2 : (c v : ℝ) < (rho F v : ℝ) + 120 * Real.sqrt ((d : ℝ) * ((rho F v : ℝ) + 3601 * d)) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h3 := sqrt_bound d hd (rho F v : ℝ) (by positivity)
  linarith

end OptimalAgnosticPAC.Dev.T2a
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

theorem edge_inv {P : Type} (y y' : P → Bool) (i : P) (h : ∀ j, j ≠ i → y j = y' j) :
    (s(y', flipAt y' i) : Sym2 (P → Bool)) = s(y, flipAt y i) := by
  by_cases hi : y i = y' i
  · have : y = y' := by
      funext j
      by_cases hj : j = i
      · subst hj; exact hi
      · exact h j hj
    rw [this]
  · have : y' = flipAt y i := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [flipAt, Function.update_self]
        revert hi; cases y j <;> cases y' j <;> simp
      · simp only [flipAt, Function.update_apply, if_neg hj]; exact (h j hj).symm
    rw [this, flipAt_flipAt]; exact Sym2.eq_swap

theorem rho_trace {X : Type} (H : Set (X → Bool)) {n : ℕ} (x : Fin n → X) (y : Fin n → Bool) :
    rho (trace H x) y = sInf ((fun h => errCount h (fun i => (x i, y i))) '' H) := by
  unfold rho
  congr 1
  ext m
  simp only [Set.mem_image, trace]
  constructor
  · rintro ⟨f, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨h, hh, ?_⟩
    simp only [errCount, DIS]; congr 1; ext i; simp [eq_comm]
  · rintro ⟨h, hh, rfl⟩
    refine ⟨_, ⟨h, hh, rfl⟩, ?_⟩
    simp only [errCount, DIS]; congr 1; ext i; simp [eq_comm]

theorem loo_of_orientation {P : Type} [Fintype P] (σ : Sym2 (P → Bool) → (P → Bool))
    (hσ : IsOrientation (cubeGraph P) σ) :
    ∃ rule : P → (P → Bool) → Bool,
      (∀ (i : P) (y y' : P → Bool), (∀ j, j ≠ i → y j = y' j) → rule i y = rule i y') ∧
      ∀ y, (Finset.univ.filter (fun i => rule i y ≠ y i)).card ≤
        outdegree (cubeGraph P) σ y := by
  refine ⟨fun i y => σ s(y, flipAt y i) i, ?_, ?_⟩
  · intro i y y' h
    simp only
    rw [edge_inv y y' i h]
  · intro y
    unfold outdegree
    refine Finset.card_le_card_of_injOn (fun i => s(y, flipAt y i)) ?_ ?_
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
      simp only [Finset.coe_filter, SimpleGraph.mem_edgeFinset, Set.mem_setOf_eq]
      have hadj : (cubeGraph P).Adj y (flipAt y i) := ⟨i, rfl⟩
      refine ⟨hadj, by simp, ?_⟩
      have hm := hσ _ ((SimpleGraph.mem_edgeSet _).2 hadj)
      intro hy
      apply hi
      rw [hy]
    · intro i _ j _ hij
      simp only at hij
      have := (Sym2.eq_iff.1 hij)
      rcases this with ⟨_, h⟩ | ⟨h, _⟩
      · by_contra hne
        have h2 := congrFun h i
        simp [flipAt, Function.update_apply, hne] at h2
      · exact absurd h (flipAt_ne y j)
end OptimalAgnosticPAC.Dev.T2b
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Learner
open OptimalAgnosticPAC.Dev.T2a OptimalAgnosticPAC.Dev.T2b

theorem chk_theorem_2 (d : ℕ) (hd : 1 ≤ d) :
    (∀ (P : Type) [Fintype P] [Nonempty P] (F : Set (P → Bool)), F.Nonempty →
      HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞) →
      ∃ σ : Sym2 (P → Bool) → (P → Bool), IsOrientation (cubeGraph P) σ ∧
        ∀ v : P → Bool, (outdegree (cubeGraph P) σ v : ℝ) ≤
          (rho F v : ℝ) + 120 * Real.sqrt ((d : ℝ) * (rho F v : ℝ)) + 7202 * (d : ℝ)) ∧
    (∀ (X : Type) (H : Set (X → Bool)), H.Nonempty →
      HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞) →
      ∀ (n : ℕ), 1 ≤ n → ∀ x : Fin n → X,
      ∃ rule : Fin n → (Fin n → Bool) → Bool, IsLOORule rule ∧
        ∀ y : Fin n → Bool,
          looRisk rule y ≤
            empMinRisk H (fun i => (x i, y i)) +
              120 * Real.sqrt ((d : ℝ) * empMinRisk H (fun i => (x i, y i)) / (n : ℝ)) +
              7202 * ((d : ℝ) / (n : ℝ))) := by
  refine ⟨fun P _ _ F hF hVC => part1 d hd P F hF hVC, ?_⟩
  intro X H hH hVC n hn x
  have : NeZero n := ⟨by omega⟩
  have hF : (trace H x).Nonempty := by
    obtain ⟨h, hh⟩ := hH
    exact ⟨_, h, hh, rfl⟩
  have hVC' : HighDimProb.Chaining.vcDim (trace H x) ≤ (d : ℕ∞) := (vc_trace_le H x).trans hVC
  obtain ⟨σ, hσ, hout⟩ := part1 d hd (Fin n) (trace H x) hF hVC'
  obtain ⟨rule, hrule, hcard⟩ := loo_of_orientation σ hσ
  refine ⟨rule, hrule, fun y => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hemp : empMinRisk H (fun i => (x i, y i)) = (rho (trace H x) y : ℝ) / n := by
    unfold empMinRisk; rw [rho_trace]
  rw [hemp]
  have h1 : ((Finset.univ.filter (fun i => rule i y ≠ y i)).card : ℝ) ≤
      (rho (trace H x) y : ℝ) + 120 * Real.sqrt ((d : ℝ) * (rho (trace H x) y : ℝ)) + 7202 * d :=
    le_trans (by exact_mod_cast hcard y) (hout y)
  have hsq : Real.sqrt ((d : ℝ) * ((rho (trace H x) y : ℝ) / n) / n) =
      Real.sqrt ((d : ℝ) * (rho (trace H x) y : ℝ)) / n := by
    have : (d : ℝ) * ((rho (trace H x) y : ℝ) / n) / n =
        (d * (rho (trace H x) y : ℝ)) / (n : ℝ) ^ 2 := by field_simp
    rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hnR.le]
  rw [hsq]
  unfold looRisk
  rw [div_le_iff₀ hnR]
  have : ((rho (trace H x) y : ℝ) / n + 120 * (Real.sqrt ((d : ℝ) * (rho (trace H x) y : ℝ)) / n) +
      7202 * ((d : ℝ) / n)) * n = (rho (trace H x) y : ℝ) +
      120 * Real.sqrt ((d : ℝ) * (rho (trace H x) y : ℝ)) + 7202 * d := by
    field_simp
  rw [this]; exact h1
end OptimalAgnosticPAC.Learner
end

theorem solution : type_of% @OptimalAgnosticPAC.Learner.chk_theorem_2 := @OptimalAgnosticPAC.Learner.chk_theorem_2
