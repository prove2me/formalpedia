-- Prove2me | solution 1 for SupplyChainTheory.lagrangian_dual_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T22:57:43.755774+00:00
-- url     : https://prove2.me/submissions/06d927cf-245b-468b-af5e-96fa144cf16b

import Mathlib
import Definitions.Def_SupplyChainTheory_location
import Theorems.Thm_SupplyChainTheory_lagrangian_subproblem
import Theorems.Thm_SupplyChainTheory_lagrangian_weak_duality

open SupplyChainTheory

/-- On any `y`, the Lagrangian objective is the UFLP cost minus the priced assignment violations. -/
private lemma lagr_eq_cost_sub {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ) :
    lagrObjective h c f lam x y = uflpCost h c f x y - ∑ i, lam i * (∑ j, y i j - 1) := by
  rw [lagrObjective, uflpCost]
  have : ∀ i, ∑ j, (h i * c i j - lam i) * y i j = ∑ j, h i * c i j * y i j - lam i * ∑ j, y i j := by
    intro i; rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp only [this, Finset.sum_sub_distrib, mul_sub, mul_one]
  ring

/-- **Lower bound for the Lagrangian objective** on `0 ≤ x ≤ 1`, `0 ≤ y ≤ x`. -/
private lemma lagr_lower {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hyx : ∀ i j, y i j ≤ x j) (hy : ∀ i j, 0 ≤ y i j) :
    ∑ j, min 0 (benefit h c lam j + f j) + ∑ i, lam i ≤ lagrObjective h c f lam x y := by
  rw [lagrObjective, Finset.sum_comm (f := fun i j => (h i * c i j - lam i) * y i j)]
  have hj : ∀ j, min 0 (benefit h c lam j + f j)
      ≤ f j * x j + ∑ i, (h i * c i j - lam i) * y i j := by
    intro j
    have hterm : ∀ i, min 0 (h i * c i j - lam i) * x j ≤ (h i * c i j - lam i) * y i j := by
      intro i
      rcases le_total 0 (h i * c i j - lam i) with hpos | hneg
      · rw [min_eq_left hpos, zero_mul]; exact mul_nonneg hpos (hy i j)
      · rw [min_eq_right hneg]; exact mul_le_mul_of_nonpos_left (hyx i j) hneg
    have hsum : benefit h c lam j * x j ≤ ∑ i, (h i * c i j - lam i) * y i j := by
      rw [benefit, Finset.sum_mul]; exact Finset.sum_le_sum (fun i _ => hterm i)
    rcases le_total 0 (benefit h c lam j + f j) with hpos | hneg
    · rw [min_eq_left hpos]; nlinarith [(hx j).1]
    · rw [min_eq_right hneg]; nlinarith [(hx j).2]
  have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
  rw [Finset.sum_add_distrib] at this
  linarith

/-- The UFLP cost is linear in `(x, y)`. -/
private lemma uflpCost_lin {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (x x' : Fin m → ℝ) (y y' : Fin n → Fin m → ℝ) (a b : ℝ) :
    uflpCost h c f (a • x + b • x') (a • y + b • y')
      = a * uflpCost h c f x y + b * uflpCost h c f x' y' := by
  simp only [uflpCost, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, mul_left_comm _ a, mul_left_comm _ b]
  ring

/-- The LP relaxation is feasible (open everything, assign to one site) and bounded below. -/
private lemma lp_nonempty {n m : ℕ} (hm : 0 < m) :
    ∃ (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ), UFLPLPFeasible x y ∧ (∀ i, ∑ j, y i j = 1) := by
  classical
  refine ⟨fun _ => 1, fun _ j => if j = ⟨0, hm⟩ then 1 else 0, ⟨fun i => by simp, fun i j => ?_,
    fun j => by norm_num, fun i j => ?_⟩, fun i => by simp⟩
  · simp only []; split_ifs <;> norm_num
  · simp only []; split_ifs <;> norm_num

private lemma lp_bddBelow {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ) :
    BddBelow {z | ∃ x y, UFLPLPFeasible x y ∧ z = uflpCost h c f x y} := by
  refine ⟨∑ j, min 0 (benefit h c 0 j + f j) + ∑ i, (0 : Fin n → ℝ) i, ?_⟩
  rintro z ⟨x, y, ⟨hsum, hyx, hx, hy⟩, rfl⟩
  have := lagr_lower h c f 0 x y hx hyx hy
  rw [lagr_eq_cost_sub] at this
  simpa using this

/-- **Separation.** Below the LP value, some multipliers make the Lagrangian bound exceed `t`. -/
private lemma exists_lagr_gt {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (hm : 0 < m) (t : ℝ) (ht : t < uflpLP h c f) : ∃ lam, t < zLR h c f lam := by
  classical
  -- The relaxed box `P = {0 ≤ y ≤ x ≤ 1}` and its image under `(x, y) ↦ ((∑ⱼ yᵢⱼ)ᵢ, cost)`.
  set P : Set ((Fin m → ℝ) × (Fin n → Fin m → ℝ)) :=
    {p | (∀ j, 0 ≤ p.1 j ∧ p.1 j ≤ 1) ∧ ∀ i j, 0 ≤ p.2 i j ∧ p.2 i j ≤ p.1 j} with hP
  set G : (Fin m → ℝ) × (Fin n → Fin m → ℝ) → (Fin n → ℝ) × ℝ :=
    fun p => (fun i => ∑ j, p.2 i j, uflpCost h c f p.1 p.2) with hG
  set K := G '' P with hK
  -- `P` is compact.
  have hPc : IsCompact P := by
    have hbox : IsCompact ((Set.univ.pi fun _ : Fin m => Set.Icc (0 : ℝ) 1) ×ˢ
        (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin m => Set.Icc (0 : ℝ) 1)) :=
      (isCompact_univ_pi fun _ => isCompact_Icc).prod
        (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)
    refine hbox.of_isClosed_subset ?_ ?_
    · have hPeq : P = (⋂ j, ({p : (Fin m → ℝ) × (Fin n → Fin m → ℝ) | 0 ≤ p.1 j} ∩ {p | p.1 j ≤ 1}))
          ∩ ⋂ i, ⋂ j, ({p | 0 ≤ p.2 i j} ∩ {p | p.2 i j ≤ p.1 j}) := by
        ext p; simp [hP, Set.mem_iInter, forall_and]
      rw [hPeq]
      refine IsClosed.inter (isClosed_iInter fun j => (isClosed_le continuous_const ?_).inter
        (isClosed_le ?_ continuous_const)) (isClosed_iInter fun i => isClosed_iInter fun j =>
        (isClosed_le continuous_const ?_).inter (isClosed_le ?_ ?_)) <;> fun_prop
    · rintro p ⟨hp1, hp2⟩
      simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
      exact ⟨fun j => hp1 j, fun i j => ⟨(hp2 i j).1, (hp2 i j).2.trans (hp1 j).2⟩⟩
  have hGc : Continuous G := by
    simp only [hG, uflpCost]; fun_prop
  have hKc : IsCompact K := hPc.image hGc
  -- `K` is convex, `G` being linear and `P` convex.
  have hKconv : Convex ℝ K := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩ _ ⟨q, ⟨hq1, hq2⟩, rfl⟩ a b ha hb hab
    refine ⟨a • p + b • q, ⟨fun j => ⟨?_, ?_⟩, fun i j => ⟨?_, ?_⟩⟩, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [(hp1 j).1, (hq1 j).1]
    · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [(hp1 j).2, (hq1 j).2]
    · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [(hp2 i j).1, (hq2 i j).1]
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      nlinarith [(hp2 i j).2, (hq2 i j).2]
    · refine Prod.ext (funext fun i => ?_) ?_
      · simp only [hG, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
      · show uflpCost h c f (a • p + b • q).1 (a • p + b • q).2
            = a * uflpCost h c f p.1 p.2 + b * uflpCost h c f q.1 q.2
        rw [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_fst, Prod.smul_snd, Prod.smul_snd]
        exact uflpCost_lin h c f _ _ _ _ a b
  -- The point `(𝟙, t)` is not in `K`: it would be an LP solution of cost `t < z_LP`.
  have hx0 : ((fun _ : Fin n => (1 : ℝ)), t) ∉ K := by
    rintro ⟨p, ⟨hp1, hp2⟩, hpeq⟩
    have hA : ∀ i, ∑ j, p.2 i j = 1 := fun i => congrFun (congrArg Prod.fst hpeq) i
    have hcost : uflpCost h c f p.1 p.2 = t := congrArg Prod.snd hpeq
    have hfeas : UFLPLPFeasible p.1 p.2 :=
      ⟨hA, fun i j => (hp2 i j).2, hp1, fun i j => (hp2 i j).1⟩
    have := csInf_le (lp_bddBelow h c f) ⟨p.1, p.2, hfeas, rfl⟩
    rw [← hcost] at ht
    exact absurd this (not_le.mpr ht)
  obtain ⟨φ, u, hφx0, hφK⟩ := geometric_hahn_banach_point_closed hKconv hKc.isClosed hx0
  -- Coordinates of the separating functional.
  set μ : Fin n → ℝ := fun i => φ ((Pi.single i 1 : Fin n → ℝ), 0) with hμ
  set α : ℝ := φ ((0 : Fin n → ℝ), 1) with hα
  have hφ : ∀ (w : Fin n → ℝ) (s : ℝ), φ (w, s) = ∑ i, w i * μ i + s * α := by
    intro w s
    have hdec : (w, s) = ∑ i, w i • ((Pi.single i 1 : Fin n → ℝ), (0 : ℝ))
        + s • ((0 : Fin n → ℝ), (1 : ℝ)) := by
      refine Prod.ext (funext fun j => ?_) ?_
      · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    rw [hdec, map_add, map_sum, map_smul]
    simp only [map_smul, smul_eq_mul, hμ, hα]
  -- An LP solution lies strictly above the level `t`, which forces `α > 0`.
  obtain ⟨x₀, y₀, hfeas₀, hA₀⟩ := lp_nonempty (n := n) hm
  have hC₀ : t < uflpCost h c f x₀ y₀ :=
    lt_of_lt_of_le ht (csInf_le (lp_bddBelow h c f) ⟨x₀, y₀, hfeas₀, rfl⟩)
  have hK₀ : G (x₀, y₀) ∈ K :=
    ⟨(x₀, y₀), ⟨hfeas₀.2.2.1, fun i j => ⟨hfeas₀.2.2.2 i j, hfeas₀.2.1 i j⟩⟩, rfl⟩
  have hsep₀ := hφK _ hK₀
  have hx0v : φ ((fun _ : Fin n => (1 : ℝ)), t) = ∑ i, μ i + t * α := by
    rw [hφ]; simp
  have hG₀ : φ (G (x₀, y₀)) = ∑ i, μ i + uflpCost h c f x₀ y₀ * α := by
    simp only [hG]; rw [hφ]; simp [hA₀]
  have hαpos : 0 < α := by
    rw [hG₀] at hsep₀; rw [hx0v] at hφx0
    nlinarith
  -- The multipliers `λᵢ = −μᵢ/α` push the Lagrangian bound above `t`.
  refine ⟨fun i => -(μ i / α), ?_⟩
  set lam : Fin n → ℝ := fun i => -(μ i / α) with hlam
  obtain ⟨⟨hyx, hx01, hy0⟩, hobj, hz⟩ := lagrangian_subproblem h c f lam
  rw [hz, ← hobj, lagr_eq_cost_sub]
  set xb := lagrX h c f lam
  set yb := lagrY h c f lam
  have hmem : G (xb, yb) ∈ K := ⟨(xb, yb), ⟨fun j => by rcases hx01 j with hj | hj <;> simp [hj],
    fun i j => ⟨hy0 i j, hyx i j⟩⟩, rfl⟩
  have hsep := hφK _ hmem
  have hGv : φ (G (xb, yb)) = ∑ i, (∑ j, yb i j) * μ i + uflpCost h c f xb yb * α := by
    simp only [hG]; rw [hφ]
  rw [hGv] at hsep; rw [hx0v] at hφx0
  have hkey : α * (∑ i, lam i * (∑ j, yb i j - 1)) = -(∑ i, (∑ j, yb i j) * μ i - ∑ i, μ i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hlam]; field_simp
  have hmul : α * t < α * (uflpCost h c f xb yb - ∑ i, lam i * (∑ j, yb i j - 1)) := by
    rw [mul_sub, hkey]; linarith
  exact lt_of_mul_lt_mul_left hmul hαpos.le

theorem solution {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (hm : 0 < m) : uflpLP h c f ≤ zLRbest h c f ∧ zLRbest h c f ≤ uflpOpt h c f := by
  -- (8.16): every Lagrangian bound is below `z*`, so the dual value is well defined.
  have hwd : ∀ lam, zLR h c f lam ≤ uflpOpt h c f := lagrangian_weak_duality h c f hm
  have hbdd : BddAbove (Set.range (zLR h c f)) := ⟨uflpOpt h c f, by rintro _ ⟨lam, rfl⟩; exact hwd lam⟩
  refine ⟨le_of_forall_lt fun t ht => ?_, csSup_le (Set.range_nonempty _) (by
    rintro _ ⟨lam, rfl⟩; exact hwd lam)⟩
  -- (8.18): below `z_LP`, separation produces multipliers with a larger Lagrangian bound.
  obtain ⟨lam, hlam⟩ := exists_lagr_gt h c f hm t ht
  exact lt_csSup_of_lt hbdd ⟨lam, rfl⟩ hlam
