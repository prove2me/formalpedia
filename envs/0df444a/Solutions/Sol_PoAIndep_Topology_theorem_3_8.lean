-- Prove2me | solution 1 for PoAIndep.Topology.theorem_3_8
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:24:18.449067+00:00
-- url     : https://prove2.me/submissions/dac59230-53d7-4eac-b9c9-c792735906fe

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model
open PoAIndep.Topology
open Filter Topology
set_option maxHeartbeats 800000

private theorem edge_nonneg {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I)
    (hf : ∀ i P, 0 ≤ f i P) (e : E) : 0 ≤ edgeFlow I f e := by
  unfold edgeFlow Finsupp.sum
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro P _
  dsimp only
  split_ifs <;> simp [hf]

private theorem moved_nonneg {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I) (hf : IsFlow I f)
    (i : Fin I.k) (P Q : List E) (δ : ℝ) (hd : δ ∈ Set.Icc 0 (f i P)) :
    ∀ j R, 0 ≤ Function.update f i (f i - Finsupp.single P δ + Finsupp.single Q δ) j R := by
  intro j R
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self, Finsupp.add_apply, Finsupp.sub_apply]
    by_cases hP : P = R
    · subst R
      by_cases hQ : Q = P <;> simp [hQ] <;> linarith [hd.1, hd.2, (hf i).1 P]
    · by_cases hQ : Q = R <;> simp [hP, hQ] <;> linarith [hd.1, (hf i).1 R]
  · simpa [Function.update_of_ne hj] using (hf j).1 R

private theorem edge_affine {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I)
    (i : Fin I.k) (P Q : List E) (δ : ℝ) (e : E) :
    edgeFlow I (Function.update f i (f i - Finsupp.single P δ + Finsupp.single Q δ)) e =
      edgeFlow I f e - (if e ∈ P then δ else 0) + (if e ∈ Q then δ else 0) := by
  classical
  have hs (g h : List E →₀ ℝ) :
      (g+h).sum (fun R a => if e ∈ R then a else 0) =
        g.sum (fun R a => if e ∈ R then a else 0) +
        h.sum (fun R a => if e ∈ R then a else 0) := by
    apply Finsupp.sum_add_index' <;> intros <;> split_ifs <;> simp
  have ht (g h : List E →₀ ℝ) :
      (g-h).sum (fun R a => if e ∈ R then a else 0) =
        g.sum (fun R a => if e ∈ R then a else 0) -
        h.sum (fun R a => if e ∈ R then a else 0) := by
    apply Finsupp.sum_sub_index <;> intros <;> split_ifs <;> simp
  unfold edgeFlow
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [Function.update_self, hs, ht]
  have hrest : ∑ j ∈ Finset.univ.erase i,
      (Function.update f i (f i - Finsupp.single P δ + Finsupp.single Q δ) j).sum
        (fun R a => if e ∈ R then a else 0) =
      ∑ j ∈ Finset.univ.erase i, (f j).sum (fun R a => if e ∈ R then a else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hrest]
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  ring

private theorem shortest {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I) (hf : IsFlow I f)
    (hn : IsNashFlow I f) (i : Fin I.k) (P Q : List E)
    (hP : IsSimplePath I.src I.tgt P (I.s i) (I.t i))
    (hQ : IsSimplePath I.src I.tgt Q (I.s i) (I.t i)) (hp : 0 < f i P) :
    pathLatency I f P ≤ pathLatency I f Q := by
  let S := Set.Icc (0 : ℝ) (f i P)
  let a := fun δ e => edgeFlow I f e - (if e ∈ P then δ else 0) + (if e ∈ Q then δ else 0)
  have ha (e : E) : Continuous (fun δ => a δ e) := by
    dsimp [a]
    apply Continuous.add
    · apply Continuous.sub continuous_const
      split_ifs <;> fun_prop
    · split_ifs <;> fun_prop
  have hnon (δ : ℝ) (hd : δ ∈ S) (e : E) : 0 ≤ a δ e := by
    dsimp only [a]
    rw [← edge_affine I f i P Q δ e]
    exact edge_nonneg I _ (moved_nonneg I f hf i P Q δ hd) e
  have hc (e : E) : ContinuousOn (fun δ => I.ℓ e (a δ e)) S :=
    (I.latency e).2.1.continuousOn.comp (ha e).continuousOn (fun δ hd => hnon δ hd e)
  have hsum : ContinuousOn (fun δ => (Q.map fun e => I.ℓ e (a δ e)).sum) S := by
    have hall : ∀ R : List E, ContinuousOn (fun δ => (R.map fun e => I.ℓ e (a δ e)).sum) S := by
      intro R
      induction R with
      | nil => simpa using continuousOn_const
      | cons e R ih => simpa [Pi.add_def] using (hc e).add ih
    exact hall Q
  have ht := (hsum.continuousWithinAt (show (0 : ℝ) ∈ S from ⟨le_rfl, hp.le⟩)).mono
    Set.Ioc_subset_Icc_self
  letI := left_nhdsWithin_Ioc_neBot hp
  have hineq : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioc 0 (f i P)),
      pathLatency I f P ≤ (Q.map fun e => I.ℓ e (a δ e)).sum := by
    filter_upwards [self_mem_nhdsWithin] with δ hd
    have hh := hn i P Q hP hQ hp δ hd
    simpa [pathLatency, edge_affine, a] using hh
  have hh := ge_of_tendsto ht hineq
  simpa [a, pathLatency] using hh

private theorem path_sum {E : Type} [Fintype E] [DecidableEq E] (P : List E)
    (hP : P.Nodup) (w : E → ℝ) :
    (∑ e, if e ∈ P then w e else 0) = (P.map w).sum := by
  induction P with
  | nil => simp
  | cons a P ih =>
    have hn := List.nodup_cons.mp hP
    have he (e : E) : (if e ∈ a :: P then w e else 0) =
        (if e = a then w e else 0) + (if e ∈ P then w e else 0) := by
      by_cases h : e = a
      · subst e; simp [hn.1]
      · simp [h]
    simp_rw [he]
    rw [Finset.sum_add_distrib, ih hn.2]
    simp

private theorem edge_path {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I) (hf : IsFlow I f) (w : E → ℝ) :
    (∑ e, w e * edgeFlow I f e) =
      ∑ i, (f i).sum (fun P a => (P.map w).sum * a) := by
  classical
  unfold edgeFlow Finsupp.sum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  have hn : P.Nodup := ((hf i).2 P hP).2.2.2.2.of_cons.of_map
  have he (e : E) : w e * (if e ∈ P then f i P else 0) =
      (if e ∈ P then w e else 0) * f i P := by split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul, path_sum P hn]

private theorem fixed_min {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f g : Flow I) (hf : IsFlow I f)
    (hfeas : IsFeasible I f) (hnash : IsNashFlow I f)
    (hg : IsFlow I g) (hgfeas : IsFeasible I g) :
    ∑ i, (f i).sum (fun P a => pathLatency I f P * a) ≤
      ∑ i, (g i).sum (fun P a => pathLatency I f P * a) := by
  classical
  have hex (i : Fin I.k) : ∃ P, 0 < f i P := by
    by_contra h
    have hz : (f i).sum (fun _ x => x) ≤ 0 := by
      unfold Finsupp.sum
      exact Finset.sum_nonpos (fun P _ => le_of_not_gt (fun hh => h ⟨P,hh⟩))
    rw [hfeas i] at hz
    linarith [I.r_pos i]
  choose P hP using hex
  apply Finset.sum_le_sum
  intro i _
  let Lc := pathLatency I f (P i)
  have hs (R : List E) (hr : 0 < f i R) :=
    (hf i).2 R (Finsupp.mem_support_iff.mpr (ne_of_gt hr))
  have he (R : List E) (hr : 0 < f i R) : pathLatency I f R = Lc :=
    le_antisymm (shortest I f hf hnash i R (P i) (hs R hr) (hs (P i) (hP i)) hr)
      (shortest I f hf hnash i (P i) R (hs (P i) (hP i)) (hs R hr) (hP i))
  have hleft : (f i).sum (fun R a => pathLatency I f R * a) = Lc * I.r i := by
    rw [← hfeas i]
    unfold Finsupp.sum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R hR
    dsimp only
    rw [he R (lt_of_le_of_ne ((hf i).1 R) (Ne.symm (Finsupp.mem_support_iff.mp hR)))]
  rw [hleft, ← hgfeas i]
  unfold Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro R hR
  exact mul_le_mul_of_nonneg_right
    (shortest I f hf hnash i (P i) R (hs (P i) (hP i)) ((hg i).2 R hR) (hP i))
    ((hg i).1 R)

private theorem marginal_cont (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ) :
    ContinuousOn (marginalCost ℓ) (Set.Ici 0) := by
  have hd : DifferentiableOn ℝ (fun x => x * ℓ x) (Set.Ici 0) :=
    differentiableOn_id.mul hℓ.1.2.1
  have hm : MonotoneOn (marginalCost ℓ) (Set.Ici 0) := hℓ.2.monotoneOn_derivWithin hd
  let S : Set ℝ := marginalCost ℓ '' Set.Ici 0
  have hS : Set.OrdConnected S := Set.ordConnected_Ici.image_derivWithin hd
  letI : Set.OrdConnected S := hS
  let f : Set.Ici (0 : ℝ) → S := fun x => ⟨marginalCost ℓ x, ⟨x, x.property, rfl⟩⟩
  have hf : Monotone f := fun x y hxy => hm x.property y.property hxy
  have hs : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  exact continuousOn_iff_continuous_restrict.mpr
    (continuous_subtype_val.comp (hf.continuous_of_surjective hs))

private theorem lambda_exists (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ) (r : ℝ) (hr : 0 < r) :
    (marginalCost ℓ 0 = ℓ 0 ∧ ℓ 0 ≤ ℓ r ∧ ℓ r ≤ marginalCost ℓ r) ∧
      ∃ lam ∈ Set.Icc (0 : ℝ) 1, marginalCost ℓ (lam * r) = ℓ r := by
  have h0 : marginalCost ℓ 0 = ℓ 0 := by
    have hd := (hasDerivWithinAt_id (0 : ℝ) (Set.Ici 0)).mul
      ((hℓ.1.2.1 0 (by simp)).hasDerivWithinAt)
    simpa [marginalCost, Pi.mul_def, id_def] using hd.derivWithin (uniqueDiffWithinAt_Ici 0)
  have hmono : ℓ 0 ≤ ℓ r := hℓ.1.2.2 (by simp) hr.le hr.le
  have hbound : ℓ r ≤ marginalCost ℓ r := by
    have h := hℓ.2.slope_le_derivWithin (by simp : (0 : ℝ) ∈ Set.Ici 0) hr.le hr
      ((differentiableOn_id.mul hℓ.1.2.1) r hr.le)
    simpa [slope_def_field, marginalCost, ne_of_gt hr] using h
  refine ⟨⟨h0, hmono, hbound⟩, ?_⟩
  have hc : ContinuousOn (marginalCost ℓ) (Set.Icc 0 r) :=
    (marginal_cont ℓ hℓ).mono (fun _ hx => hx.1)
  obtain ⟨y, hy, he⟩ := intermediate_value_Icc hr.le hc ⟨by simpa [h0] using hmono, hbound⟩
  refine ⟨y/r, ⟨div_nonneg hy.1 hr.le, (div_le_one hr).2 hy.2⟩, ?_⟩
  simpa [ne_of_gt hr] using he

private theorem denominator_le_one (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ)
    (x : ℝ) (hx : 0 < x) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hp : 0 < ℓ x) :
    ENNReal.ofReal (lam * (ℓ (lam*x)/ℓ x) + (1-lam)) ≤ 1 := by
  have h0 : 0 ≤ lam*x := mul_nonneg hlam.1 hx.le
  have h1 : lam*x ≤ x := by nlinarith [hlam.2]
  have hm : ℓ (lam*x) ≤ ℓ x := hℓ.1.2.2 h0 hx.le h1
  have hd : ℓ (lam*x)/ℓ x ≤ 1 := (div_le_one hp).2 hm
  apply (ENNReal.ofReal_le_one).2
  nlinarith [mul_nonneg hlam.1 (sub_nonneg.mpr hd)]

private theorem denominator_pos (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ)
    (x : ℝ) (hx : 0 < x) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hp : 0 < ℓ x) : 0 < lam * (ℓ (lam*x)/ℓ x) + (1-lam) := by
  rcases eq_or_lt_of_le hlam.2 with he | he
  · subst lam
    simp [ne_of_gt hp]
  · have hn := mul_nonneg hlam.1 (div_nonneg
      (hℓ.1.1 (lam*x) (mul_nonneg hlam.1 hx.le)) hp.le)
    linarith

private theorem alpha_ge_one (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) :
    1 ≤ anarchyValue L := by
  obtain ⟨ℓ, hmem, y, hy, hne⟩ := hL.1
  have hp : 0 < ℓ (y+1) := lt_of_lt_of_le
    (lt_of_le_of_ne ((hL.2 ℓ hmem).1.1 y hy) (Ne.symm hne))
    ((hL.2 ℓ hmem).1.2.2 hy (show 0 ≤ y+1 by linarith) (show y ≤ y+1 by linarith))
  obtain ⟨lam, hlam, he⟩ := (lambda_exists ℓ (hL.2 ℓ hmem) (y+1) (by linarith)).2
  have hb := denominator_le_one ℓ (hL.2 ℓ hmem) (y+1) (by linarith) lam hlam hp
  calc
    1 ≤ (ENNReal.ofReal (lam * (ℓ (lam*(y+1))/ℓ (y+1)) + (1-lam)))⁻¹ :=
      ENNReal.one_le_inv.mpr hb
    _ ≤ anarchyValue L := by
      unfold anarchyValue anarchyValueFn
      refine le_iSup_of_le ℓ (le_iSup_of_le hmem (le_iSup_of_le (y+1)
        (le_iSup_of_le (by linarith : 0 < y+1) (le_iSup_of_le hp
          (le_iSup_of_le lam (le_iSup_of_le hlam (le_iSup_of_le he ?_)))))))
      rw [ENNReal.ofReal_inv_of_pos (denominator_pos ℓ (hL.2 ℓ hmem)
        (y+1) (by linarith) lam hlam hp)]

private theorem tangent_bound (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ)
    (z y : ℝ) (hz : 0 ≤ z) (hy : 0 ≤ y) :
    z * ℓ z + marginalCost ℓ z * (y-z) ≤ y * ℓ y := by
  have hd := differentiableOn_id.mul hℓ.1.2.1
  rcases lt_trichotomy z y with h | h | h
  · have hb := hℓ.2.derivWithin_le_slope hz hy h (hd z hz)
    rw [slope_def_field] at hb
    have hh := (le_div_iff₀ (sub_pos.mpr h)).mp hb
    dsimp [marginalCost] at *
    nlinarith
  · subst y; simp
  · have hb := hℓ.2.slope_le_derivWithin hy hz h (hd z hz)
    rw [slope_def_field] at hb
    have hh := (div_le_iff₀ (sub_pos.mpr h)).mp hb
    dsimp [marginalCost] at *
    nlinarith

private theorem edge_bound (L : Set (ℝ → ℝ)) (hL : IsStandardClass L)
    (htop : anarchyValue L ≠ ⊤) (ℓ : ℝ → ℝ) (hmem : ℓ ∈ L)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * ℓ x ≤ (anarchyValue L).toReal * (y*ℓ y - (y-x)*ℓ x) := by
  have hℓ := hL.2 ℓ hmem
  have hA : 0 ≤ (anarchyValue L).toReal := ENNReal.toReal_nonneg
  by_cases hx0 : x = 0
  · subst x
    have hm : ℓ 0 ≤ ℓ y := hℓ.1.2.2 (by simp) hy hy
    have hh := mul_nonneg hy (sub_nonneg.mpr hm)
    simp only [zero_mul, sub_zero]
    exact mul_nonneg hA (by nlinarith)
  by_cases hl0 : ℓ x = 0
  · simp only [hl0, mul_zero, sub_zero]
    exact mul_nonneg hA (mul_nonneg hy (hℓ.1.1 y hy))
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hlp : 0 < ℓ x := lt_of_le_of_ne (hℓ.1.1 x hx) (Ne.symm hl0)
  obtain ⟨lam, hlam, hsolve⟩ := (lambda_exists ℓ hℓ x hxp).2
  let d := lam * (ℓ (lam*x)/ℓ x) + (1-lam)
  have hd : 0 < d := denominator_pos ℓ hℓ x hxp lam hlam hlp
  have halpha : ENNReal.ofReal d⁻¹ ≤ anarchyValue L := by
    unfold anarchyValue anarchyValueFn
    exact le_iSup_of_le ℓ (le_iSup_of_le hmem (le_iSup_of_le x
      (le_iSup_of_le hxp (le_iSup_of_le hlp (le_iSup_of_le lam
        (le_iSup_of_le hlam (le_iSup_of_le hsolve le_rfl)))))))
  have had : 1 ≤ (anarchyValue L).toReal * d := by
    have h := (ENNReal.ofReal_le_iff_le_toReal htop).mp halpha
    rw [inv_eq_one_div] at h
    exact (div_le_iff₀ hd).mp h
  have ht := tangent_bound ℓ hℓ (lam*x) y (mul_nonneg hlam.1 hx) hy
  rw [hsolve] at ht
  have hid : d*(x*ℓ x) = (lam*x)*ℓ (lam*x) + (1-lam)*x*ℓ x := by
    dsimp [d]
    field_simp
  have hb : d*(x*ℓ x) ≤ y*ℓ y - (y-x)*ℓ x := by nlinarith [hid]
  have hmul := mul_le_mul_of_nonneg_left hb hA
  have hmul' := mul_le_mul_of_nonneg_right had (mul_nonneg hx hlp.le)
  nlinarith

theorem PoAIndep.Topology.theorem_3_8 (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) :
    ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (I : Instance V E),
      InClass I L → ∀ f g : Flow I, IsFlow I f → IsFeasible I f → IsNashFlow I f →
        IsFlow I g → IsFeasible I g → 0 < cost I g →
          ENNReal.ofReal (cost I f / cost I g) ≤ anarchyValue L := by
  intro V E _ _ _ _ I hmem f g hf hfeas hn hg hgfeas hcost
  by_cases htop : anarchyValue L = ⊤
  · simp [htop]
  have hnash : (∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I f e) ≤
      ∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I g e := by
    rw [edge_path I f hf, edge_path I g hg]
    exact fixed_min I f g hf hfeas hn hg hgfeas
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun e _ =>
    edge_bound L hL htop (I.ℓ e) (hmem e) (edgeFlow I f e) (edgeFlow I g e)
      (edge_nonneg I f (fun i => (hf i).1) e) (edge_nonneg I g (fun i => (hg i).1) e))
  have hcf : cost I f = ∑ e, edgeFlow I f e * I.ℓ e (edgeFlow I f e) := by
    rw [show (∑ e, edgeFlow I f e * I.ℓ e (edgeFlow I f e)) =
        ∑ e, I.ℓ e (edgeFlow I f e)*edgeFlow I f e by
      apply Finset.sum_congr rfl; intro e _; ring]
    exact (edge_path I f hf _).symm
  have hcg : cost I g = ∑ e, edgeFlow I g e * I.ℓ e (edgeFlow I g e) := by
    rw [show (∑ e, edgeFlow I g e * I.ℓ e (edgeFlow I g e)) =
        ∑ e, I.ℓ e (edgeFlow I g e)*edgeFlow I g e by
      apply Finset.sum_congr rfl; intro e _; ring]
    exact (edge_path I g hg _).symm
  have herr : 0 ≤ ∑ e, (edgeFlow I g e - edgeFlow I f e)*I.ℓ e (edgeFlow I f e) := by
    simp_rw [sub_mul, mul_comm (edgeFlow I g _), mul_comm (edgeFlow I f _)]
    rw [Finset.sum_sub_distrib]
    exact sub_nonneg.mpr hnash
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← hcf, ← hcg] at hb
  have hfinal : cost I f ≤ (anarchyValue L).toReal * cost I g := by
    nlinarith [mul_nonneg (show 0 ≤ (anarchyValue L).toReal from ENNReal.toReal_nonneg) herr]
  exact (ENNReal.ofReal_le_iff_le_toReal htop).mpr ((div_le_iff₀ hcost).mpr hfinal)

theorem solution (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) :
    ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (I : Instance V E),
      InClass I L → ∀ f g : Flow I, IsFlow I f → IsFeasible I f → IsNashFlow I f →
        IsFlow I g → IsFeasible I g → 0 < cost I g →
          ENNReal.ofReal (cost I f / cost I g) ≤ anarchyValue L :=
  PoAIndep.Topology.theorem_3_8 L hL

#print axioms solution
