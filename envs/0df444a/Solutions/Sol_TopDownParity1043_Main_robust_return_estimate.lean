-- Prove2me | solution 1 for TopDownParity1043.Main.robust_return_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:18:26.006909+00:00
-- url     : https://prove2.me/submissions/d23b8058-5078-4ead-825d-f3ac40ae389d

import Mathlib
import Definitions.Def_TopDownParity1043_Main_Limit
import Theorems.Thm_TopDownParity1043_Main_lemma_4
import Theorems.Thm_TopDownParity1043_Main_lemma_10
import Theorems.Thm_TopDownParity1043_Main_random_restriction_coupling
import Theorems.Thm_TopDownParity1043_Main_random_set_restriction

set_option autoImplicit false
open scoped NNReal ENNReal
open TopDownParity1043.Main

private theorem deficit_count_iff {V : Type} [Fintype V] [DecidableEq V]
    (t : ℕ) (X : Finset (V → Bool)) (hX : X.Nonempty) (k : ℝ) :
    setDeficit t X ≤ k ↔ (2 : ℝ) ^ ((t : ℝ)-k) ≤ X.card := by
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  unfold setDeficit
  rw [← Real.le_logb_iff_rpow_le (by norm_num) hxpos]
  constructor <;> intro h <;> linarith

private theorem deficit_nonneg_of_count {V : Type} [Fintype V] [DecidableEq V]
    (t : ℕ) (X : Finset (V → Bool)) (hc : X.card ≤ 2 ^ t) : 0 ≤ setDeficit t X := by
  unfold setDeficit
  apply sub_nonneg.mpr
  by_cases he : X.card = 0
  · simp [he]
  · have hxpos : (0 : ℝ) < X.card := by exact_mod_cast Nat.pos_of_ne_zero he
    rw [Real.logb_le_iff_le_rpow (by norm_num) hxpos, Real.rpow_natCast]
    exact_mod_cast hc

private theorem set_deficit_nonneg {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) : 0 ≤ setDeficit (Fintype.card V) X := by
  apply deficit_nonneg_of_count
  simpa using Finset.card_le_univ X

private theorem fibre_card_bound {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (x : V → Bool) (S : Finset V) :
    (fibre X x S).card ≤ 2 ^ S.card := by
  classical
  let f : fibre X x S → (S → Bool) := fun y => project S y.1
  have hinj : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · exact congrFun hyz ⟨i,hi⟩
    · have hy : InSubcube x S y.1 := (Finset.mem_filter.mp y.2).2
      have hz : InSubcube x S z.1 := (Finset.mem_filter.mp z.2).2
      exact (hy i hi).trans (hz i hi).symm
  have hc := Fintype.card_le_of_injective f hinj
  simpa using hc

private theorem fibre_deficit_nonneg {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (x : V → Bool) (S : Finset V) :
    0 ≤ setDeficit S.card (fibre X x S) :=
  deficit_nonneg_of_count S.card (fibre X x S) (fibre_card_bound X x S)

private theorem uniform_deficit {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (hX : X.Nonempty) :
    lawDeficit (PMF.uniformOfFinset X hX) = setDeficit (Fintype.card V) X := by
  classical
  have hcap : ∀ x : V → Bool, (PMF.uniformOfFinset X hX x).toReal ≤ (X.card : ℝ)⁻¹ := by
    intro x
    rw [PMF.uniformOfFinset_apply]
    split_ifs <;> simp <;> positivity
  have hbdd : BddAbove (Set.range fun x : V → Bool => (PMF.uniformOfFinset X hX x).toReal) := by
    exact ⟨(X.card : ℝ)⁻¹, by rintro a ⟨x,rfl⟩; exact hcap x⟩
  have hsup : (⨆ x : V → Bool, (PMF.uniformOfFinset X hX x).toReal) = (X.card : ℝ)⁻¹ := by
    apply le_antisymm (ciSup_le hcap)
    obtain ⟨x,hx⟩ := hX
    have h := le_ciSup hbdd x
    simpa [PMF.uniformOfFinset_apply_of_mem ⟨x,hx⟩ hx] using h
  unfold lawDeficit SamplingAC0.minEntropy setDeficit
  rw [hsup]
  simp [Real.logb_inv]

private theorem projection_uniform {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (hX : X.Nonempty) (R : Finset V) (z : R → Bool) :
    (projectionLaw (PMF.uniformOfFinset X hX) R z).toReal =
      ((X.filter fun x => project R x = z).card : ℝ) / X.card := by
  classical
  have hENN : projectionLaw (PMF.uniformOfFinset X hX) R z =
      ((X.filter fun x => project R x = z).card : ℝ≥0∞) / X.card := by
    unfold projectionLaw
    rw [PMF.map_apply, tsum_fintype]
    calc
      _ = ∑ x : V → Bool,
          if x ∈ X.filter (fun x => project R x = z) then (X.card : ℝ≥0∞)⁻¹ else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hmem : x ∈ X <;> by_cases hz : project R x = z <;>
          simp [PMF.uniformOfFinset_apply, hmem, hz, eq_comm]
      _ = ∑ x ∈ X.filter (fun x => project R x = z), (X.card : ℝ≥0∞)⁻¹ := by
        rw [Finset.sum_ite_mem]
        simp
      _ = ((X.filter fun x => project R x = z).card : ℝ≥0∞) / X.card := by
        simp [div_eq_mul_inv]
  rw [hENN, ENNReal.toReal_div]
  simp

private theorem strong_pattern_count {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (hX : X.Nonempty) (k : ℝ) (hk : 1 ≤ k)
    (hdef : setDeficit (Fintype.card V) X ≤ 64 * k)
    (R : Finset V)
    (hlight : (lightCount (PMF.uniformOfFinset X hX) R (64*k) : ℝ) ≤
      (2 : ℝ) ^ ((R.card : ℝ)-64*k)) :
    ((Finset.univ.filter fun z : R → Bool =>
      ((X.filter fun x => project R x = z).card : ℝ) <
        (2 : ℝ) ^ ((Fintype.card V : ℝ) - R.card - 194*k)).card : ℝ) ≤
      (2 : ℝ) ^ ((R.card : ℝ)-k-6) := by
  classical
  have hsize : (2 : ℝ) ^ ((Fintype.card V : ℝ)-64*k) ≤ X.card :=
    (deficit_count_iff (Fintype.card V) X hX (64*k)).mp hdef
  have hXpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hsubset :
      (Finset.univ.filter fun z : R → Bool =>
        ((X.filter fun x => project R x = z).card : ℝ) <
          (2 : ℝ) ^ ((Fintype.card V : ℝ) - R.card - 194*k)) ⊆
        (Finset.univ.filter fun z : R → Bool =>
          (projectionLaw (PMF.uniformOfFinset X hX) R z).toReal ≤
            (2 : ℝ) ^ (-(R.card : ℝ)-2*(64*k)-2)) := by
    intro z hz
    have hzbad := (Finset.mem_filter.mp hz).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [projection_uniform X hX]
    apply (div_le_iff₀ hXpos).mpr
    have hpow : (2 : ℝ) ^ ((Fintype.card V : ℝ)-R.card-194*k) ≤
        2 ^ (-(R.card : ℝ)-2*(64*k)-2) * 2 ^ ((Fintype.card V : ℝ)-64*k) := by
      rw [← Real.rpow_add (by norm_num)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    exact hzbad.le.trans (hpow.trans (mul_le_mul_of_nonneg_left hsize (by positivity)))
  have hcard :
      (((Finset.univ.filter fun z : R → Bool =>
        ((X.filter fun x => project R x = z).card : ℝ) <
          (2 : ℝ) ^ ((Fintype.card V : ℝ) - R.card - 194*k)).card) : ℝ) ≤
        lightCount (PMF.uniformOfFinset X hX) R (64*k) := by
    unfold lightCount
    exact_mod_cast Finset.card_le_card hsubset
  apply (hcard.trans hlight).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith

private theorem strong_patterns_law {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (hX : X.Nonempty) (k : ℝ) (hk : 1 ≤ k)
    (hdef : setDeficit (Fintype.card V) X ≤ 64*k)
    (r : Bias) (hr : (r : ℝ) ≤ (32768*k)⁻¹) :
    (63 : ℝ) / 64 ≤ setProb r (fun R : Finset V =>
      ((Finset.univ.filter fun z : R → Bool =>
        ((X.filter fun x => project R x = z).card : ℝ) <
          (2 : ℝ) ^ ((Fintype.card V : ℝ) - R.card - 194*k)).card : ℝ) ≤
        (2 : ℝ) ^ ((R.card : ℝ)-k-6)) := by
  classical
  have hbound : (r : ℝ) ≤ (512*(64*k))⁻¹ := by convert hr using 1 <;> ring
  have hD : lawDeficit (PMF.uniformOfFinset X hX) ≤ 64*k := by
    rw [uniform_deficit]
    exact hdef
  have hl := lemma_10 V (64*k) (by linarith) r hbound (PMF.uniformOfFinset X hX) hD
  apply hl.trans
  apply Finset.sum_le_sum
  intro R hR
  have himp := strong_pattern_count X hX k hk hdef R
  by_cases hlight : (lightCount (PMF.uniformOfFinset X hX) R (64*k) : ℝ) ≤
      (2 : ℝ) ^ ((R.card : ℝ)-64*k)
  · simp [hlight, himp hlight]
  · simp only [if_neg hlight]
    split_ifs
    · unfold setWeight
      positivity [r.property.1, r.property.2]
    · exact le_rfl

private theorem good_fibres_mass {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (hX : X.Nonempty) (S : Finset V)
    (k : ℝ) (hk : 1 ≤ k) (hdef : setDeficit (Fintype.card V) X ≤ k) :
    (63 : ℝ) / 64 ≤
      ((X.filter fun x => setDeficit S.card (fibre X x S) ≤ 64*k).card : ℝ) / X.card := by
  classical
  let D : (V → Bool) → ℝ := fun x => setDeficit S.card (fibre X x S)
  let B : Finset (V → Bool) := X.filter fun x => ¬D x ≤ 64*k
  have hmean := (lemma_4 V X hX S).trans hdef
  change (∑ x ∈ X, D x) / X.card ≤ k at hmean
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hsumle := (div_le_iff₀ hxpos).mp hmean
  have hsumlower : 64*k*(B.card : ℝ) ≤ ∑ x ∈ X, D x := by
    calc
      64*k*(B.card : ℝ) = ∑ _ ∈ B, (64*k : ℝ) := by simp [mul_comm]
      _ ≤ ∑ x ∈ B, D x := by
        apply Finset.sum_le_sum
        intro x hx
        exact (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
      _ ≤ ∑ x ∈ X, D x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro x hx hxb
        exact fibre_deficit_nonneg X x S
  have hcard := Finset.card_filter_add_card_filter_not (s := X) (fun x => D x ≤ 64*k)
  have hcardR : ((X.filter fun x => D x ≤ 64*k).card : ℝ) + B.card = X.card := by
    exact_mod_cast hcard
  apply (le_div_iff₀ hxpos).mpr
  change 63 / 64 * (X.card : ℝ) ≤ ((X.filter fun x => D x ≤ 64*k).card : ℝ)
  nlinarith

private theorem mean_comm {A B : Type} [DecidableEq A] [Fintype B]
    (X : Finset A) (w : B → ℝ) (f : A → B → ℝ) :
    (∑ x ∈ X, ∑ b : B, w b * f x b) / X.card =
      ∑ b : B, w b * ((∑ x ∈ X, f x b) / X.card) := by
  simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc]
  rw [Finset.sum_comm]

private def subcubeEquiv {V : Type} [Fintype V] [DecidableEq V]
    (x : V → Bool) (S : Finset V) :
    {y : V → Bool // InSubcube x S y} ≃ (S → Bool) where
  toFun y := project S y.1
  invFun z := ⟨fun i => if hi : i ∈ S then z ⟨i,hi⟩ else x i, by
    intro i hi
    simp [hi]⟩
  left_inv y := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · simp [hi, project]
    · simpa [hi] using (y.2 i hi).symm
  right_inv z := by
    funext i
    simp [project, i.2]

open Classical in
private theorem subcube_card {V : Type} [Fintype V] [DecidableEq V]
    (x : V → Bool) (S : Finset V) :
    (Finset.univ.filter (InSubcube x S)).card = 2 ^ S.card := by
  classical
  rw [← Fintype.card_subtype, Fintype.card_congr (subcubeEquiv x S)]
  simp

private theorem project_inj_on_subcube {V : Type} [Fintype V] [DecidableEq V]
    (x : V → Bool) (S : Finset V) :
    Set.InjOn (project S) {y | InSubcube x S y} := by
  intro y hy z hz he
  funext i
  by_cases hi : i ∈ S
  · exact congrFun he ⟨i,hi⟩
  · exact (hy i hi).trans (hz i hi).symm

private theorem projected_fibre_card {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (x : V → Bool) (S : Finset V) :
    ((fibre X x S).image (project S)).card = (fibre X x S).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro y hy z hz he
  exact project_inj_on_subcube x S (Finset.mem_filter.mp hy).2
    (Finset.mem_filter.mp hz).2 he

private theorem fibre_projection_match {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (x y : V → Bool) (S Q : Finset V)
    (hQ : Q ⊆ S) (hy : InSubcube x S y) :
    (fibre X x S).filter (fun z => project (S \ Q) z = project (S \ Q) y) =
      fibre X y Q := by
  classical
  ext z
  simp only [fibre, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hz,hxz⟩,he⟩
    refine ⟨hz, ?_⟩
    intro i hi
    by_cases hiS : i ∈ S
    · exact congrFun he ⟨i,Finset.mem_sdiff.mpr ⟨hiS,hi⟩⟩
    · exact (hxz i hiS).trans (hy i hiS).symm
  · rintro ⟨hz,hyz⟩
    refine ⟨⟨hz, ?_⟩, ?_⟩
    · intro i hi
      exact (hyz i (fun hiQ => hi (hQ hiQ))).trans (hy i hi)
    · funext i
      exact hyz i (Finset.mem_sdiff.mp i.2).2

private noncomputable def patternEquiv {V : Type} [DecidableEq V]
    (S : Finset V) (R : Finset S) :
    (R → Bool) ≃ (R.map (Function.Embedding.subtype _) → Bool) :=
  Equiv.arrowCongr (Finset.equivMap (Function.Embedding.subtype _) R) (Equiv.refl Bool)

private theorem project_pattern_iff {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) (R : Finset S) (y : V → Bool) (z : R → Bool) :
    project R (project S y) = z ↔
      project (R.map (Function.Embedding.subtype _)) y = patternEquiv S R z := by
  let e := Finset.equivMap (Function.Embedding.subtype _) R
  change project R (project S y) = z ↔
    project (R.map (Function.Embedding.subtype _)) y = fun i => z (e.symm i)
  constructor
  · intro h
    funext i
    have hi := congrFun h (e.symm i)
    have he : ((e.symm i).1.1 : V) = i.1 := congrArg Subtype.val (e.apply_symm_apply i)
    simpa only [project, he] using hi
  · intro h
    funext i
    have hi := congrFun h (e i)
    change y i.1.1 = z (e.symm (e i)) at hi
    simpa only [Equiv.symm_apply_apply, project] using hi

private theorem projected_pattern_card {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (x : V → Bool) (S : Finset V)
    (R : Finset S) (z : R → Bool) :
    (((fibre X x S).image (project S)).filter
      (fun y => project R y = z)).card =
    ((fibre X x S).filter (fun y =>
      project (R.map (Function.Embedding.subtype _)) y = patternEquiv S R z)).card := by
  classical
  rw [Finset.filter_image]
  have he : (fibre X x S).filter (fun y => project R (project S y) = z) =
      (fibre X x S).filter (fun y =>
        project (R.map (Function.Embedding.subtype _)) y = patternEquiv S R z) := by
    apply Finset.filter_congr
    intro y hy
    exact project_pattern_iff S R y z
  rw [he]
  apply Finset.card_image_iff.mpr
  intro y hy w hw heq
  exact project_inj_on_subcube x S (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2 heq

open Classical in
private theorem projected_bad_card {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (x : V → Bool) (S : Finset V)
    (R : Finset S) (a : ℝ) :
    (Finset.univ.filter fun z : R → Bool =>
      ((((fibre X x S).image (project S)).filter (fun y => project R y = z)).card : ℝ) < a).card =
    (Finset.univ.filter fun z : R.map (Function.Embedding.subtype _) → Bool =>
      (((fibre X x S).filter (fun y => project (R.map (Function.Embedding.subtype _)) y = z)).card : ℝ) < a).card := by
  classical
  apply Finset.card_bij (fun z _ => patternEquiv S R z)
  · intro z hz
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, projected_pattern_card] using hz
  · intro z hz w hw he
    exact (patternEquiv S R).injective he
  · intro w hw
    refine ⟨(patternEquiv S R).symm w, ?_, (patternEquiv S R).apply_symm_apply w⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, projected_pattern_card,
      Equiv.apply_symm_apply] using hw

private def subcubePatternEquiv {V : Type} [Fintype V] [DecidableEq V]
    (x : V → Bool) (P R : Finset V) (hR : R ⊆ P) (z : R → Bool) :
    {y : V → Bool // InSubcube x P y ∧ project R y = z} ≃ (↥(P \ R) → Bool) where
  toFun y i := y.1 i
  invFun w := ⟨fun i => if hiR : i ∈ R then z ⟨i,hiR⟩ else
      if hiP : i ∈ P then w ⟨i,Finset.mem_sdiff.mpr ⟨hiP,hiR⟩⟩ else x i, by
    constructor
    · intro i hi
      have hiR : i ∉ R := fun hh => hi (hR hh)
      simp [hi,hiR]
    · funext i
      simp [project,i.2]⟩
  left_inv y := by
    apply Subtype.ext
    funext i
    by_cases hiR : i ∈ R
    · have h := congrFun y.2.2 ⟨i,hiR⟩
      simpa [hiR,project] using h.symm
    · by_cases hiP : i ∈ P
      · simp [hiR,hiP]
      · simpa [hiR,hiP] using (y.2.1 i hiP).symm
  right_inv w := by
    funext i
    simp [(Finset.mem_sdiff.mp i.2).1,(Finset.mem_sdiff.mp i.2).2]

open Classical in
private theorem subcube_pattern_card {V : Type} [Fintype V] [DecidableEq V]
    (x : V → Bool) (P R : Finset V) (hR : R ⊆ P) (z : R → Bool) :
    (Finset.univ.filter fun y : V → Bool => InSubcube x P y ∧ project R y = z).card =
      2 ^ (P.card-R.card) := by
  classical
  rw [← Fintype.card_subtype, Fintype.card_congr (subcubePatternEquiv x P R hR z)]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
    Finset.card_sdiff_of_subset hR]

open Classical in
private theorem subcube_bad_card {V : Type} [Fintype V] [DecidableEq V]
    (x : V → Bool) (P R : Finset V) (hR : R ⊆ P) (B : (R → Bool) → Prop) :
    (Finset.univ.filter fun y : V → Bool => InSubcube x P y ∧ B (project R y)).card =
      (Finset.univ.filter B).card * 2 ^ (P.card-R.card) := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ.filter (InSubcube x P)) (Finset.univ.filter B) (project R)
  have hf : ∀ z : R → Bool,
      ((Finset.univ.filter (InSubcube x P)).filter (fun y => project R y = z)).card =
      2 ^ (P.card-R.card) := by
    intro z
    rw [Finset.filter_filter]
    exact subcube_pattern_card x P R hR z
  simp_rw [hf] at h
  simpa only [Finset.sum_const, smul_eq_mul, Finset.filter_filter, Finset.mem_filter,
    Finset.mem_univ, true_and] using h.symm

open Classical in
private theorem fibre_bad_law {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (x : V → Bool) (hx : x ∈ X) (S : Finset V)
    (k : ℝ) (hk : 1 ≤ k) (hdef : setDeficit S.card (fibre X x S) ≤ 64*k)
    (r : Bias) (hr : (r : ℝ) ≤ (32768*k)⁻¹) :
    (63 : ℝ)/64 ≤ ∑ R : Finset S, setWeight r R *
      if ((Finset.univ.filter fun z : R.map (Function.Embedding.subtype _) → Bool =>
        (((fibre X x S).filter (fun y => project (R.map (Function.Embedding.subtype _)) y = z)).card : ℝ) <
          (2 : ℝ)^((S.card : ℝ)-R.card-194*k)).card : ℝ) ≤
            (2 : ℝ)^((R.card : ℝ)-k-6) then 1 else 0 := by
  classical
  have hxF : x ∈ fibre X x S := by simp [fibre,InSubcube,hx]
  have hF : ((fibre X x S).image (project S)).Nonempty :=
    ⟨project S x, Finset.mem_image.mpr ⟨x,hxF,rfl⟩⟩
  have hdefF : setDeficit (Fintype.card S) ((fibre X x S).image (project S)) ≤ 64*k := by
    simpa only [setDeficit, projected_fibre_card, Fintype.card_coe] using hdef
  have hl := strong_patterns_law ((fibre X x S).image (project S)) hF k hk hdefF r hr
  simpa only [setProb, projected_bad_card, Fintype.card_coe, mul_ite, mul_one, mul_zero] using hl

open Classical in
private theorem fibre_bad_law_ambient {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (x : V → Bool) (hx : x ∈ X) (S : Finset V)
    (k : ℝ) (hk : 1 ≤ k) (hdef : setDeficit S.card (fibre X x S) ≤ 64*k)
    (r : Bias) (hr : (r : ℝ) ≤ (32768*k)⁻¹) :
    (63 : ℝ)/64 ≤ ∑ T : Finset V, setWeight r T *
      if ((Finset.univ.filter fun z : ↥(T ∩ S) → Bool =>
        (((fibre X x S).filter (fun y => project (T ∩ S) y = z)).card : ℝ) <
          (2 : ℝ)^((S.card : ℝ)-(T ∩ S).card-194*k)).card : ℝ) ≤
            (2 : ℝ)^(((T ∩ S).card : ℝ)-k-6) then 1 else 0 := by
  classical
  rw [random_set_restriction V r S (fun R =>
    if ((Finset.univ.filter fun z : R → Bool =>
      (((fibre X x S).filter (fun y => project R y = z)).card : ℝ) <
        (2 : ℝ)^((S.card : ℝ)-R.card-194*k)).card : ℝ) ≤
          (2 : ℝ)^((R.card : ℝ)-k-6) then 1 else 0)]
  simpa only [Finset.card_map] using fibre_bad_law X x hx S k hk hdef r hr

private noncomputable def patternGood {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (x : V → Bool) (S R : Finset V) (k : ℝ) : Prop := by
  classical
  exact ((Finset.univ.filter fun z : R → Bool =>
    (((fibre X x S).filter (fun y => project R y = z)).card : ℝ) <
      (2 : ℝ)^((S.card : ℝ)-R.card-194*k)).card : ℝ) ≤
        (2 : ℝ)^((R.card : ℝ)-k-6)

private noncomputable def returnGood {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (x : V → Bool) (P Q : Finset V) (k : ℝ) : Prop := by
  classical
  exact ((Finset.univ.filter fun y : V → Bool => InSubcube x P y ∧
    ((fibre X y Q).card : ℝ) < (2 : ℝ)^((Q.card : ℝ)-194*k)).card : ℝ) ≤
      (2 : ℝ)^((P.card : ℝ)-k-6)

private theorem pattern_implies_return {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (x : V → Bool) (P Q : Finset V) (k : ℝ)
    (h : patternGood X x (P ∪ Q) (P \ Q) k) : returnGood X x P Q k := by
  classical
  let S := P ∪ Q
  let R := P \ Q
  have hR : R ⊆ P := Finset.sdiff_subset
  have hR' : S \ Q = R := by ext i; simp [S,R]; tauto
  have hcard : S.card = R.card + Q.card := by
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_union_right (s₁ := P) (s₂ := Q))
    simpa only [S, R, Finset.union_sdiff_right] using hh.symm
  have hcardReal : (S.card : ℝ) - R.card = Q.card := by
    have hh : (S.card : ℝ) = R.card + Q.card := by exact_mod_cast hcard
    linarith
  let B : (R → Bool) → Prop := fun z =>
    (((fibre X x S).filter (fun y => project R y = z)).card : ℝ) <
      (2 : ℝ)^((Q.card : ℝ)-194*k)
  have hfilter : (Finset.univ.filter fun y : V → Bool => InSubcube x P y ∧
      ((fibre X y Q).card : ℝ) < (2 : ℝ)^((Q.card : ℝ)-194*k)) =
      (Finset.univ.filter fun y : V → Bool => InSubcube x P y ∧ B (project R y)) := by
    apply Finset.filter_congr
    intro y hy
    by_cases hyP : InSubcube x P y
    · have hyS : InSubcube x S y := by
        intro i hi
        exact hyP i (fun hh => hi (Finset.mem_union_left Q hh))
      have hh := fibre_projection_match X x y S Q Finset.subset_union_right hyS
      rw [hR'] at hh
      simp only [hyP, true_and, B, hh]
    · simp [hyP]
  have hb : ((Finset.univ.filter B).card : ℝ) ≤ (2 : ℝ)^((R.card : ℝ)-k-6) := by
    change ((Finset.univ.filter fun z : R → Bool =>
      (((fibre X x S).filter (fun y => project R y = z)).card : ℝ) <
        (2 : ℝ)^((S.card : ℝ)-R.card-194*k)).card : ℝ) ≤
          (2 : ℝ)^((R.card : ℝ)-k-6) at h
    rw [hcardReal] at h
    exact h
  unfold returnGood
  rw [hfilter, subcube_bad_card x P R hR B, Nat.cast_mul]
  calc
    _ ≤ (2 : ℝ)^((R.card : ℝ)-k-6) * (2 ^ (P.card-R.card) : ℕ) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2 : ℝ)^((P.card : ℝ)-k-6) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
        ← Real.rpow_add (by norm_num), Nat.cast_sub (Finset.card_le_card hR)]
      congr 1
      ring

private theorem weight_nonneg {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (R : Finset V) : 0 ≤ setWeight p R := by
  unfold setWeight
  exact mul_nonneg (pow_nonneg p.property.1 _) (pow_nonneg (sub_nonneg.mpr p.property.2) _)

private theorem weight_sum {V : Type} [Fintype V] [DecidableEq V] (p : Bias) :
    ∑ R : Finset V, setWeight p R = 1 := by
  simp only [setWeight, Fintype.sum_pow_mul_eq_add_pow, add_sub_cancel, one_pow]

private theorem prob_nonneg {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (E : Finset V → Prop) : 0 ≤ setProb p E := by
  classical
  apply Finset.sum_nonneg
  intro R hR
  split_ifs <;> positivity [weight_nonneg p R]

private theorem prob_le_one {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (E : Finset V → Prop) : setProb p E ≤ 1 := by
  classical
  calc
    _ ≤ ∑ R : Finset V, setWeight p R := by
      apply Finset.sum_le_sum
      intro R hR
      split_ifs
      · exact le_rfl
      · exact weight_nonneg p R
    _ = 1 := weight_sum p

private theorem good_pattern_average {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (hX : X.Nonempty) (S : Finset V)
    (k : ℝ) (hk : 1 ≤ k) (hdef : setDeficit (Fintype.card V) X ≤ k)
    (r : Bias) (hr : (r : ℝ) ≤ (32768*k)⁻¹) :
    (31 : ℝ)/32 ≤ (∑ x ∈ X, setProb r (fun T => patternGood X x S (T ∩ S) k)) / X.card := by
  classical
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hpoint : ∀ x ∈ X,
      (if setDeficit S.card (fibre X x S) ≤ 64*k then (63 : ℝ)/64 else 0) ≤
        setProb r (fun T => patternGood X x S (T ∩ S) k) := by
    intro x hx
    split_ifs with hg
    · convert fibre_bad_law_ambient X x hx S k hk hg r hr using 1
      unfold setProb patternGood
      simp only [mul_ite, mul_one, mul_zero]
    · exact prob_nonneg r _
  have hs := Finset.sum_le_sum hpoint
  have hgood := good_fibres_mass X hX S k hk hdef
  have heq : (∑ x ∈ X, if setDeficit S.card (fibre X x S) ≤ 64*k then (63 : ℝ)/64 else 0) =
      ((X.filter fun x => setDeficit S.card (fibre X x S) ≤ 64*k).card : ℝ) * (63/64) := by
    rw [← Finset.sum_filter]
    simp
  rw [heq] at hs
  have hh := mul_le_mul_of_nonneg_right hgood (show (0 : ℝ) ≤ 63/64 by norm_num)
  apply (le_div_iff₀ hxpos).mpr
  have hh' := (le_div_iff₀ hxpos).mp (show (63 : ℝ)/64*(63/64) ≤
      ((X.filter fun x => setDeficit S.card (fibre X x S) ≤ 64*k).card : ℝ) * (63/64) / X.card by
    simpa only [div_mul_eq_mul_div] using hh)
  nlinarith

private theorem return_good_average {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (hX : X.Nonempty)
    (k : ℝ) (hk : 1 ≤ k) (hdef : setDeficit (Fintype.card V) X ≤ k)
    (p q s r : Bias) (hs : (s : ℝ) = (p : ℝ)+(q : ℝ)-(p : ℝ)*(q : ℝ))
    (hsr : (s : ℝ)*(r : ℝ) = (p : ℝ)*(1-(q : ℝ)))
    (hr : (r : ℝ) ≤ (32768*k)⁻¹) :
    (31 : ℝ)/32 ≤ (∑ x ∈ X, ∑ P : Finset V,
      setWeight p P * setProb q (fun Q => returnGood X x P Q k)) / X.card := by
  classical
  let a := fun x S => setProb r (fun T => patternGood X x S (S ∩ T) k)
  have havg : ∀ S : Finset V, (31 : ℝ)/32 ≤ (∑ x ∈ X, a x S) / X.card := by
    intro S
    simpa only [a, Finset.inter_comm] using good_pattern_average X hX S k hk hdef r hr
  have hcoupling : ∀ x : V → Bool,
      (∑ S : Finset V, setWeight s S * a x S) =
        ∑ P : Finset V, setWeight p P * setProb q (fun Q => patternGood X x (P ∪ Q) (P \ Q) k) := by
    intro x
    have hh := random_restriction_coupling V p q s r hs hsr
      (fun S R => if patternGood X x S R k then (1 : ℝ) else 0)
    simpa only [a, setProb, mul_ite, mul_one, mul_zero] using hh.symm
  calc
    (31 : ℝ)/32 = ∑ S : Finset V, setWeight s S * (31/32) := by
      rw [← Finset.sum_mul, weight_sum, one_mul]
    _ ≤ ∑ S : Finset V, setWeight s S * ((∑ x ∈ X, a x S) / X.card) := by
      apply Finset.sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_left (havg S) (weight_nonneg s S)
    _ = (∑ x ∈ X, ∑ S : Finset V, setWeight s S * a x S) / X.card := (mean_comm X (setWeight s) a).symm
    _ = (∑ x ∈ X, ∑ P : Finset V, setWeight p P *
        setProb q (fun Q => patternGood X x (P ∪ Q) (P \ Q) k)) / X.card := by
      simp_rw [hcoupling]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro P hP
      apply mul_le_mul_of_nonneg_left _ (weight_nonneg p P)
      unfold setProb
      apply Finset.sum_le_sum
      intro Q hQ
      by_cases hg : patternGood X x (P ∪ Q) (P \ Q) k
      · simp only [if_pos hg, if_pos (pattern_implies_return X x P Q k hg)]
        exact le_rfl
      · simp only [if_neg hg]
        split_ifs
        · exact weight_nonneg q Q
        · exact le_rfl

open Classical in
theorem solution (V : Type) [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (hX : X.Nonempty)
    (k : ℝ) (hk : 1 ≤ k) (hdef : setDeficit (Fintype.card V) X ≤ k)
    (p q s r : Bias) (hs : (s : ℝ) = (p : ℝ)+(q : ℝ)-(p : ℝ)*(q : ℝ))
    (hsr : (s : ℝ)*(r : ℝ) = (p : ℝ)*(1-(q : ℝ)))
    (hr : (r : ℝ) ≤ (32768*k)⁻¹) :
    (31 : ℝ)/32 ≤ (∑ x ∈ X, ∑ P : Finset V, setWeight p P *
      setProb q (fun Q =>
        ((Finset.univ.filter fun y : V → Bool => InSubcube x P y ∧
          ((fibre X y Q).card : ℝ) < (2 : ℝ)^((Q.card : ℝ)-194*k)).card : ℝ) ≤
            (2 : ℝ)^((P.card : ℝ)-k-6))) / X.card := by
  exact return_good_average X hX k hk hdef p q s r hs hsr hr
