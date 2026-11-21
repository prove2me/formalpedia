-- Prove2me | solution 1 for OptimalAgnosticPAC.Learner.eq_13_symmetrized_loo
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:42:41.369304+00:00
-- url     : https://prove2.me/submissions/012f1341-055b-4299-aade-00cb84240487

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Cube
import Theorems.Thm_OptimalAgnosticPAC_Learner_lemma_2_1
import Theorems.Thm_OptimalAgnosticPAC_Learner_eq_4_rademacher_width
import Theorems.Thm_OptimalAgnosticPAC_Learner_hall_orientation
import Definitions.Def_OptimalAgnosticPAC_Learner_Risk
import Definitions.Def_OptimalAgnosticPAC_Learner_Score

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
namespace OptimalAgnosticPAC.Dev.Eq13
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.T2a OptimalAgnosticPAC.Dev.T2b

section rule
variable (d : ℕ) (hd : 1 ≤ d) {P : Type} [Fintype P] [Nonempty P]

noncomputable def ori (F : Set (P → Bool)) :
    Sym2 (P → Bool) → (P → Bool) :=
  if h : F.Nonempty ∧ HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞) then
    Classical.choose (part1 d hd P F h.1 h.2)
  else fun _ _ => false

theorem ori_spec (F : Set (P → Bool)) (h : F.Nonempty ∧ HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞)) :
    IsOrientation (cubeGraph (P)) (ori d hd F) ∧
      ∀ v : P → Bool, (outdegree (cubeGraph (P)) (ori d hd F) v : ℝ) ≤
        (rho F v : ℝ) + 120 * Real.sqrt ((d : ℝ) * (rho F v : ℝ)) + 7202 * (d : ℝ) := by
  unfold ori; rw [dif_pos h]; exact Classical.choose_spec (part1 d hd P F h.1 h.2)

noncomputable def lrule (F : Set (P → Bool)) :
    P → (P → Bool) → Bool :=
  if h : F.Nonempty ∧ HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞) then
    Classical.choose (loo_of_orientation (ori d hd F) (ori_spec d hd F h).1)
  else fun _ _ => false

theorem lrule_indep (F : Set (P → Bool)) (i : P) (y y' : P → Bool)
    (h : ∀ j, j ≠ i → y j = y' j) : lrule d hd F i y = lrule d hd F i y' := by
  unfold lrule
  split_ifs with hh
  · exact (Classical.choose_spec (loo_of_orientation (ori d hd F) (ori_spec d hd F hh).1)).1 i y y' h
  · rfl

theorem lrule_count (F : Set (P → Bool)) (h : F.Nonempty ∧ HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞))
    (y : P → Bool) :
    ((Finset.univ.filter (fun i => lrule d hd F i y ≠ y i)).card : ℝ) ≤
      (rho F y : ℝ) + 120 * Real.sqrt ((d : ℝ) * (rho F y : ℝ)) + 7202 * (d : ℝ) := by
  have h1 : lrule d hd F = Classical.choose (loo_of_orientation (ori d hd F) (ori_spec d hd F h).1) := by
    unfold lrule; rw [dif_pos h]
  rw [h1]
  exact le_trans (by exact_mod_cast (Classical.choose_spec
    (loo_of_orientation (ori d hd F) (ori_spec d hd F h).1)).2 y) ((ori_spec d hd F h).2 y)

variable (m : ℕ) {X : Type} (H : Set (X → Bool))

noncomputable def ee (z : Fin (m+1) → X) (y : Fin (m+1) → Bool) (ρ : Equiv.Perm (Fin (m+1)))
    (j : Fin (m+1)) : ℝ :=
  sgn (lrule d hd (trace H (z ∘ ρ)) (ρ.symm j) (y ∘ ρ))

theorem ee_comp (z : Fin (m+1) → X) (y : Fin (m+1) → Bool) (τ π : Equiv.Perm (Fin (m+1)))
    (j : Fin (m+1)) :
    ee d hd m H (z ∘ τ) (y ∘ τ) π j = ee d hd m H z y (τ * π) (τ j) := by
  unfold ee
  have h1 : (z ∘ τ) ∘ π = z ∘ ⇑(τ * π) := rfl
  have h2 : (y ∘ τ) ∘ π = y ∘ ⇑(τ * π) := rfl
  have h3 : (τ * π).symm (τ j) = π.symm j := by
    rw [Equiv.symm_apply_eq]; simp [Equiv.Perm.mul_apply]
  rw [h1, h2, h3]

theorem ee_indep (z : Fin (m+1) → X) (y y' : Fin (m+1) → Bool) (ρ : Equiv.Perm (Fin (m+1)))
    (j : Fin (m+1)) (h : ∀ k, k ≠ j → y k = y' k) :
    ee d hd m H z y ρ j = ee d hd m H z y' ρ j := by
  unfold ee
  rw [lrule_indep d hd _ (ρ.symm j) (y ∘ ρ) (y' ∘ ρ)]
  intro k hk
  apply h
  intro hkj
  apply hk
  rw [← hkj]; simp

theorem abs_ee (z : Fin (m+1) → X) (y : Fin (m+1) → Bool) (ρ : Equiv.Perm (Fin (m+1)))
    (j : Fin (m+1)) : |ee d hd m H z y ρ j| = 1 := by
  unfold ee sgn; split_ifs <;> simp

end rule

section samples
variable {X : Type} (H : Set (X → Bool)) (d : ℕ) (hd : 1 ≤ d)

noncomputable def zz {m : ℕ} (S : Fin m → X × Bool) (x : X) : Fin (m+1) → X :=
  Fin.lastCases (motive := fun _ => X) x (fun k => (S k).1)

noncomputable def yy {m : ℕ} (S : Fin m → X × Bool) : Fin (m+1) → Bool :=
  Fin.lastCases (motive := fun _ => Bool) false (fun k => (S k).2)

noncomputable def qq (m : ℕ) (S : Fin m → X × Bool) (x : X) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin (m+1))) : ℝ)⁻¹ *
    ∑ π : Equiv.Perm (Fin (m+1)), ee d hd m H (zz S x) (yy S) π (Fin.last m)

def tauFun {m : ℕ} (i : Fin (m+1)) : Fin (m+1) → Fin (m+1) :=
  Fin.lastCases (motive := fun _ => Fin (m+1)) i (fun j => i.succAbove j)

theorem tauFun_inj {m : ℕ} (i : Fin (m+1)) : Function.Injective (tauFun i) := by
  intro a b hab
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rfl
    | cast b =>
      simp only [tauFun, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
      exact absurd hab (Fin.succAbove_ne i b).symm
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      simp only [tauFun, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
      exact absurd hab (Fin.succAbove_ne i a)
    | cast b =>
      simp only [tauFun, Fin.lastCases_castSucc] at hab
      rw [Fin.succAbove_right_inj] at hab
      rw [hab]

noncomputable def tau {m : ℕ} (i : Fin (m+1)) : Equiv.Perm (Fin (m+1)) :=
  Equiv.ofBijective (tauFun i) (Finite.injective_iff_bijective.1 (tauFun_inj i))

theorem tau_last {m : ℕ} (i : Fin (m+1)) : tau i (Fin.last m) = i := by
  show tauFun i (Fin.last m) = i
  simp [tauFun]

theorem tau_cast {m : ℕ} (i : Fin (m+1)) (j : Fin m) : tau i (Fin.castSucc j) = i.succAbove j := by
  show tauFun i (Fin.castSucc j) = _
  simp [tauFun]

def sigFun {m : ℕ} (σ : Equiv.Perm (Fin m)) : Fin (m+1) → Fin (m+1) :=
  Fin.lastCases (motive := fun _ => Fin (m+1)) (Fin.last m) (fun j => Fin.castSucc (σ j))

theorem sigFun_inj {m : ℕ} (σ : Equiv.Perm (Fin m)) : Function.Injective (sigFun σ) := by
  intro a b hab
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rfl
    | cast b =>
      simp only [sigFun, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
      exact absurd hab (Fin.castSucc_lt_last _).ne'
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      simp only [sigFun, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
      exact absurd hab (Fin.castSucc_lt_last _).ne
    | cast b =>
      simp only [sigFun, Fin.lastCases_castSucc] at hab
      have := σ.injective (Fin.castSucc_injective _ hab)
      rw [this]

noncomputable def sig {m : ℕ} (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m+1)) :=
  Equiv.ofBijective (sigFun σ) (Finite.injective_iff_bijective.1 (sigFun_inj σ))

theorem sig_last {m : ℕ} (σ : Equiv.Perm (Fin m)) : sig σ (Fin.last m) = Fin.last m := by
  show sigFun σ (Fin.last m) = _
  simp [sigFun]

theorem zz_deleteObs {m : ℕ} (S : Fin (m+1) → X × Bool) (i : Fin (m+1)) :
    zz (deleteObs S i) (S i).1 = (fun j => (S j).1) ∘ (tau i) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [zz, tau_last]
  | cast j => simp [zz, tau_cast, deleteObs]

theorem yy_deleteObs {m : ℕ} (S : Fin (m+1) → X × Bool) (i : Fin (m+1)) (k : Fin (m+1))
    (hk : k ≠ Fin.last m) : yy (deleteObs S i) k = ((fun j => (S j).2) ∘ (tau i)) k := by
  induction k using Fin.lastCases with
  | last => exact absurd rfl hk
  | cast j => simp [yy, tau_cast, deleteObs]

theorem qq_term {m : ℕ} (S : Fin (m+1) → X × Bool) (i : Fin (m+1)) :
    qq H d hd m (deleteObs S i) (S i).1 =
      (Fintype.card (Equiv.Perm (Fin (m+1))) : ℝ)⁻¹ *
        ∑ ρ : Equiv.Perm (Fin (m+1)), ee d hd m H (fun j => (S j).1) (fun j => (S j).2) ρ i := by
  unfold qq
  congr 1
  rw [← Fintype.sum_equiv (Equiv.mulLeft (tau i))
    (fun π => ee d hd m H (fun j => (S j).1) (fun j => (S j).2) (tau i * π) i)
    (fun ρ => ee d hd m H (fun j => (S j).1) (fun j => (S j).2) ρ i) (fun _ => rfl)]
  refine Finset.sum_congr rfl (fun π _ => ?_)
  rw [zz_deleteObs, ee_indep d hd m H _ _ ((fun j => (S j).2) ∘ (tau i)) π (Fin.last m)
    (fun k hk => yy_deleteObs S i k hk), ee_comp, tau_last]

theorem qq_symm {m : ℕ} (S : Fin m → X × Bool) (σ : Equiv.Perm (Fin m)) (x : X) :
    qq H d hd m (S ∘ σ) x = qq H d hd m S x := by
  unfold qq
  congr 1
  have hz : zz (S ∘ σ) x = zz S x ∘ sig σ := by
    funext j
    induction j using Fin.lastCases with
    | last => simp [zz, sig, sigFun]
    | cast j => simp [zz, sig, sigFun]
  have hy : yy (S ∘ σ) = yy S ∘ sig σ := by
    funext j
    induction j using Fin.lastCases with
    | last => simp [yy, sig, sigFun]
    | cast j => simp [yy, sig, sigFun]
  rw [← Fintype.sum_equiv (Equiv.mulLeft (sig σ))
    (fun π => ee d hd m H (zz S x) (yy S) (sig σ * π) (Fin.last m))
    (fun ρ => ee d hd m H (zz S x) (yy S) ρ (Fin.last m)) (fun _ => rfl)]
  refine Finset.sum_congr rfl (fun π _ => ?_)
  rw [hz, hy, ee_comp, sig_last]

theorem qq_mem {m : ℕ} (S : Fin m → X × Bool) (x : X) : qq H d hd m S x ∈ Set.Icc (-1 : ℝ) 1 := by
  have hc : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin (m+1))) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hs : |∑ π : Equiv.Perm (Fin (m+1)), ee d hd m H (zz S x) (yy S) π (Fin.last m)| ≤
      (Fintype.card (Equiv.Perm (Fin (m+1))) : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp [abs_ee]
  unfold qq
  rw [Set.mem_Icc, ← abs_le, abs_mul, abs_of_pos (inv_pos.2 hc), inv_mul_le_iff₀ hc]
  simpa using hs

theorem abs_sgn_sub (a b : Bool) : |sgn a - sgn b| = if a ≠ b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [sgn, abs_of_nonneg]

theorem errCount_perm {n : ℕ} (h : X → Bool) (S : Fin n → X × Bool) (ρ : Equiv.Perm (Fin n)) :
    errCount h (fun i => S (ρ i)) = errCount h S := by
  unfold errCount
  exact Finset.card_equiv ρ (by simp)

theorem rho_perm {m : ℕ} (S : Fin (m+1) → X × Bool) (ρ : Equiv.Perm (Fin (m+1))) :
    (rho (trace H ((fun j => (S j).1) ∘ ρ)) ((fun j => (S j).2) ∘ ρ) : ℝ) =
      ((m : ℝ) + 1) * empMinRisk H S := by
  rw [rho_trace]
  have : (fun h => errCount h (fun i => (((fun j => (S j).1) ∘ ρ) i, ((fun j => (S j).2) ∘ ρ) i))) =
      fun h => errCount h S := by
    funext h
    exact errCount_perm h S ρ
  rw [this]
  unfold empMinRisk
  have : ((m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

theorem alg (d e n T : ℝ) (hn : 0 < n)
    (hT : T ≤ 2 * (n * e + 120 * Real.sqrt (d * (n * e)) + 7202 * d)) :
    (1 / (2 * n)) * T ≤ e + 120 * Real.sqrt (d * e / n) + 7202 * (d / n) := by
  have hsq : Real.sqrt (d * e / n) = Real.sqrt (d * (n * e)) / n := by
    have : d * e / n = (d * (n * e)) / n ^ 2 := by field_simp
    rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hn.le]
  rw [hsq, one_div, inv_mul_le_iff₀ (by positivity)]
  have : 2 * n * (e + 120 * (Real.sqrt (d * (n * e)) / n) + 7202 * (d / n)) =
      2 * (n * e + 120 * Real.sqrt (d * (n * e)) + 7202 * d) := by
    field_simp
  rw [this]; exact hT

theorem qq_bound (hH : H.Nonempty) (hVC : HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞)) {m : ℕ}
    (S : Fin (m+1) → X × Bool) :
    (1 / (2 * ((m : ℝ) + 1))) * ∑ i, |qq H d hd m (deleteObs S i) (S i).1 - sgn (S i).2| ≤
      empMinRisk H S + 120 * Real.sqrt ((d : ℝ) * empMinRisk H S / ((m : ℝ) + 1)) +
        7202 * ((d : ℝ) / ((m : ℝ) + 1)) := by
  set z : Fin (m+1) → X := fun j => (S j).1 with hz
  set y : Fin (m+1) → Bool := fun j => (S j).2 with hy
  set C : ℝ := (Fintype.card (Equiv.Perm (Fin (m+1))) : ℝ) with hC
  have hc : 0 < C := by rw [hC]; exact_mod_cast Fintype.card_pos
  have step1 : ∀ i, |qq H d hd m (deleteObs S i) (S i).1 - sgn (S i).2| ≤
      C⁻¹ * ∑ ρ : Equiv.Perm (Fin (m+1)), |ee d hd m H z y ρ i - sgn (y i)| := by
    intro i
    rw [qq_term]
    show |_ - sgn (y i)| ≤ _
    have : C⁻¹ * (∑ ρ : Equiv.Perm (Fin (m+1)), ee d hd m H z y ρ i) - sgn (y i) =
        C⁻¹ * ∑ ρ : Equiv.Perm (Fin (m+1)), (ee d hd m H z y ρ i - sgn (y i)) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← hC]
      field_simp
    rw [this, abs_mul, abs_of_pos (inv_pos.2 hc)]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.2 hc).le
  set e := empMinRisk H S with he
  have hn : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have step2 : ∀ ρ : Equiv.Perm (Fin (m+1)), ∑ i, |ee d hd m H z y ρ i - sgn (y i)| ≤
      2 * (((m : ℝ) + 1) * e + 120 * Real.sqrt ((d : ℝ) * (((m : ℝ) + 1) * e)) + 7202 * d) := by
    intro ρ
    rw [← Equiv.sum_comp ρ]
    have hF : (trace H (z ∘ ρ)).Nonempty ∧
        HighDimProb.Chaining.vcDim (trace H (z ∘ ρ)) ≤ (d : ℕ∞) := by
      refine ⟨?_, (vc_trace_le H _).trans hVC⟩
      obtain ⟨h, hh⟩ := hH
      exact ⟨_, h, hh, rfl⟩
    have hcnt := lrule_count d hd _ hF (y ∘ ρ)
    rw [rho_perm H S ρ] at hcnt
    refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul_of_nonneg_left hcnt (by norm_num : (0:ℝ) ≤ 2)) le_rfl)
    unfold ee
    simp only [Equiv.symm_apply_apply]
    have : ∀ k, |sgn (lrule d hd (trace H (z ∘ ρ)) k (y ∘ ρ)) - sgn (y (ρ k))| =
        if lrule d hd (trace H (z ∘ ρ)) k (y ∘ ρ) ≠ (y ∘ ρ) k then 2 else 0 := fun k =>
      abs_sgn_sub _ _
    simp only [Function.comp_apply] at this
    simp only [this]
    rw [Finset.sum_ite]
    simp
    ring
  calc (1 / (2 * ((m : ℝ) + 1))) * ∑ i, |qq H d hd m (deleteObs S i) (S i).1 - sgn (S i).2|
      ≤ (1 / (2 * ((m : ℝ) + 1))) *
        (2 * (((m : ℝ) + 1) * e + 120 * Real.sqrt ((d : ℝ) * (((m : ℝ) + 1) * e)) + 7202 * d)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ i, |qq H d hd m (deleteObs S i) (S i).1 - sgn (S i).2|
            ≤ ∑ i, C⁻¹ * ∑ ρ : Equiv.Perm (Fin (m+1)), |ee d hd m H z y ρ i - sgn (y i)| :=
              Finset.sum_le_sum (fun i _ => step1 i)
          _ = C⁻¹ * ∑ ρ : Equiv.Perm (Fin (m+1)), ∑ i, |ee d hd m H z y ρ i - sgn (y i)| := by
              rw [← Finset.mul_sum, Finset.sum_comm]
          _ ≤ C⁻¹ * ∑ ρ : Equiv.Perm (Fin (m+1)),
                (2 * (((m : ℝ) + 1) * e + 120 * Real.sqrt ((d : ℝ) * (((m : ℝ) + 1) * e)) + 7202 * d)) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ρ _ => step2 ρ)) (inv_pos.2 hc).le
          _ = _ := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              rw [← hC]; field_simp
    _ ≤ _ := by
        have := alg (d : ℝ) e ((m : ℝ) + 1) _ hn le_rfl
        exact this

end samples

section meas
variable {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ) (hd : 1 ≤ d)

theorem meas_comp_trace {A : Type} [MeasurableSpace A] {n : ℕ} (htrace : TraceMeasurable H)
    (u : A → Fin n → X) (hu : Measurable u) (v : A → Fin n → Bool) (hv : Measurable v)
    (g : Set (Fin n → Bool) → (Fin n → Bool) → ℝ) :
    Measurable (fun a => g (trace H (u a)) (v a)) := by
  let _ : MeasurableSpace (Set (Fin n → Bool)) := ⊤
  have : MeasurableSingletonClass (Set (Fin n → Bool)) :=
    ⟨fun _ => by simp [MeasurableSpace.measurableSet_top]⟩
  have h1 : Measurable (fun a => (trace H (u a), v a)) := by
    apply measurable_to_countable'
    rintro ⟨T, w⟩
    have : (fun a => (trace H (u a), v a)) ⁻¹' {(T, w)} =
        (u ⁻¹' {x | trace H x = T}) ∩ v ⁻¹' {w} := by
      ext a; simp [Prod.ext_iff]
    rw [this]
    exact (hu (htrace n T)).inter (hv (measurableSet_singleton w))
  exact (measurable_of_countable (fun p : Set (Fin n → Bool) × (Fin n → Bool) => g p.1 p.2)).comp h1

theorem meas_zz (m : ℕ) (j : Fin (m+1)) :
    Measurable (fun p : (Fin m → X × Bool) × X => zz p.1 p.2 j) := by
  induction j using Fin.lastCases with
  | last => simpa [zz] using measurable_snd
  | cast k =>
    simp only [zz, Fin.lastCases_castSucc]
    exact measurable_fst.comp ((measurable_pi_apply k).comp measurable_fst)

theorem meas_yy (m : ℕ) (j : Fin (m+1)) :
    Measurable (fun p : (Fin m → X × Bool) × X => yy p.1 j) := by
  induction j using Fin.lastCases with
  | last => simp [yy]
  | cast k =>
    simp only [yy, Fin.lastCases_castSucc]
    exact measurable_snd.comp ((measurable_pi_apply k).comp measurable_fst)

theorem meas_qq (htrace : TraceMeasurable H) (m : ℕ) :
    Measurable (fun p : (Fin m → X × Bool) × X => qq H d hd m p.1 p.2) := by
  unfold qq
  refine Measurable.const_mul (Finset.measurable_sum _ (fun π _ => ?_)) _
  unfold ee
  exact meas_comp_trace H htrace (fun p : (Fin m → X × Bool) × X => zz p.1 p.2 ∘ π)
    (measurable_pi_iff.2 (fun k => meas_zz m (π k)))
    (fun p : (Fin m → X × Bool) × X => yy p.1 ∘ π)
    (measurable_pi_iff.2 (fun k => meas_yy m (π k)))
    (fun T v => sgn (lrule d hd T (π.symm (Fin.last m)) v))

end meas
end OptimalAgnosticPAC.Dev.Eq13

namespace OptimalAgnosticPAC.Learner
open MeasureTheory
open scoped Classical

theorem chk_eq_13_symmetrized_loo {X : Type} [MeasurableSpace X] (H : Set (X → Bool))
    (hH : H.Nonempty) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞))
    (hmeas : ∀ h ∈ H, Measurable h) (htrace : TraceMeasurable H) :
    ∃ q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ, IsLOOScore H d q := by
  open OptimalAgnosticPAC.Dev.Eq13 in
  exact ⟨fun m S x => qq H d hd m S x, ⟨fun m S x => qq_mem H d hd S x,
    fun m S π x => qq_symm H d hd S π x, fun m => meas_qq H d hd htrace m,
    fun m S => qq_bound H d hd hH hVC S⟩⟩

end OptimalAgnosticPAC.Learner
end

theorem solution : type_of% @OptimalAgnosticPAC.Learner.chk_eq_13_symmetrized_loo := @OptimalAgnosticPAC.Learner.chk_eq_13_symmetrized_loo
