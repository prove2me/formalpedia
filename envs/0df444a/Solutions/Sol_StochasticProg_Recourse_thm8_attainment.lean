-- Prove2me | solution 1 for StochasticProg.Recourse.thm8_attainment
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T14:34:36.916483+00:00
-- url     : https://prove2.me/submissions/da6f8a5a-eeca-4964-97ee-ac3ee91bcccd

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance

set_option autoImplicit false

namespace SolD74bda2c

open Matrix

/-- Fundamental theorem of LP (standard form, attainment): a linear objective bounded below
on a nonempty set `{z ≥ 0, L z = d}` attains its minimum. -/
theorem lp_attain {ι F : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup F] [Module ℝ F]
    (L : (ι → ℝ) →ₗ[ℝ] F) (d : F) (cc : ι → ℝ)
    (hne : ∃ z : ι → ℝ, (∀ i, 0 ≤ z i) ∧ L z = d)
    (hbdd : ∃ v : ℝ, ∀ z : ι → ℝ, (∀ i, 0 ≤ z i) → L z = d → v ≤ cc ⬝ᵥ z) :
    ∃ z : ι → ℝ, ((∀ i, 0 ≤ z i) ∧ L z = d) ∧
      ∀ z' : ι → ℝ, (∀ i, 0 ≤ z' i) → L z' = d → cc ⬝ᵥ z ≤ cc ⬝ᵥ z' := by
  obtain ⟨v, hv⟩ := hbdd
  -- good points: feasible with no nonzero kernel vector supported on the support
  let Good : (ι → ℝ) → Prop := fun z => ((∀ i, 0 ≤ z i) ∧ L z = d) ∧
    ∀ w : ι → ℝ, (∀ i, z i = 0 → w i = 0) → L w = 0 → w = 0
  have reduce : ∀ n : ℕ, ∀ z : ι → ℝ, (∀ i, 0 ≤ z i) → L z = d →
      (Finset.univ.filter (fun i => z i ≠ 0)).card = n →
      ∃ z', Good z' ∧ cc ⬝ᵥ z' ≤ cc ⬝ᵥ z := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
    intro z hz0 hzd hcard
    by_cases hg : ∀ w : ι → ℝ, (∀ i, z i = 0 → w i = 0) → L w = 0 → w = 0
    · exact ⟨z, ⟨⟨hz0, hzd⟩, hg⟩, le_rfl⟩
    push Not at hg
    obtain ⟨w, hwsupp, hwL, hw0⟩ := hg
    -- a direction that decreases the objective and hits a new zero
    have key : ∀ u : ι → ℝ, (∀ i, z i = 0 → u i = 0) → L u = 0 → 0 ≤ cc ⬝ᵥ u →
        (∃ i, 0 < u i) → ∃ z', Good z' ∧ cc ⬝ᵥ z' ≤ cc ⬝ᵥ z := by
      intro u husupp huL hucc ⟨j, hj⟩
      have hsne : (Finset.univ.filter (fun i => 0 < u i)).Nonempty :=
        ⟨j, by simp [hj]⟩
      obtain ⟨i0, hi0, hmin⟩ :=
        (Finset.univ.filter (fun i => 0 < u i)).exists_min_image (fun i => z i / u i) hsne
      have hui0 : 0 < u i0 := (Finset.mem_filter.mp hi0).2
      set t := z i0 / u i0 with ht
      have ht0 : 0 ≤ t := div_nonneg (hz0 i0) hui0.le
      set z'' := z - t • u with hz''
      have hz''i : ∀ i, z'' i = z i - t * u i := by intro i; simp [hz'']
      have hz''0 : ∀ i, 0 ≤ z'' i := by
        intro i
        rw [hz''i]
        by_cases hui : 0 < u i
        · have := hmin i (by simp [hui])
          have : t * u i ≤ z i := by
            rw [← le_div_iff₀ hui]; exact this
          linarith
        · push Not at hui
          have : t * u i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hui
          linarith [hz0 i]
      have hz''d : L z'' = d := by
        rw [hz'', map_sub, map_smul, huL, smul_zero, sub_zero, hzd]
      have hz''cc : cc ⬝ᵥ z'' ≤ cc ⬝ᵥ z := by
        rw [hz'', dotProduct_sub, dotProduct_smul, smul_eq_mul]
        nlinarith
      have hsub : Finset.univ.filter (fun i => z'' i ≠ 0) ⊂
          Finset.univ.filter (fun i => z i ≠ 0) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨i0, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            intro hzi0
            have := husupp i0 hzi0
            linarith
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
            rw [hz''i, ht, div_mul_cancel₀ _ hui0.ne']
            ring
        · intro i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro h1 h2
          apply h1
          rw [hz''i, h2, husupp i h2]
          ring
      have hlt := Finset.card_lt_card hsub
      obtain ⟨z', hz'g, hz'cc⟩ := IH _ (hcard ▸ hlt) z'' hz''0 hz''d rfl
      exact ⟨z', hz'g, hz'cc.trans hz''cc⟩
    have unb : ∀ u : ι → ℝ, L u = 0 → (∀ i, u i ≤ 0) → 0 < cc ⬝ᵥ u → False := by
      intro u huL hule hpos
      have hvz := hv z hz0 hzd
      set t := (cc ⬝ᵥ z - v + 1) / (cc ⬝ᵥ u) with ht
      have ht0 : 0 ≤ t := div_nonneg (by linarith) hpos.le
      have hfeas0 : ∀ i, 0 ≤ (z - t • u) i := by
        intro i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have : t * u i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 (hule i)
        linarith [hz0 i]
      have hfeasd : L (z - t • u) = d := by
        rw [map_sub, map_smul, huL, smul_zero, sub_zero, hzd]
      have h := hv _ hfeas0 hfeasd
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ht, div_mul_cancel₀ _ hpos.ne'] at h
      linarith
    have hwsuppn : ∀ i, z i = 0 → (-w) i = 0 := by
      intro i hi; simp [hwsupp i hi]
    have hwLn : L (-w) = 0 := by rw [map_neg, hwL, neg_zero]
    rcases lt_trichotomy (cc ⬝ᵥ w) 0 with hneg | hzero | hpos
    · have hpos' : 0 < cc ⬝ᵥ (-w) := by rw [dotProduct_neg]; linarith
      by_cases hex : ∃ i, 0 < (-w) i
      · exact key (-w) hwsuppn hwLn hpos'.le hex
      · push Not at hex
        exact (unb (-w) hwLn hex hpos').elim
    · obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
        by_contra hcon; push Not at hcon; exact hw0 (funext hcon)
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · exact key (-w) hwsuppn hwLn (by rw [dotProduct_neg]; linarith) ⟨i, by simp; linarith⟩
      · exact key w hwsupp hwL hzero.ge ⟨i, hgt⟩
    · by_cases hex : ∃ i, 0 < w i
      · exact key w hwsupp hwL hpos.le hex
      · push Not at hex
        exact (unb w hwL hex hpos).elim
  -- finiteness of good points
  have hfin : {z : ι → ℝ | Good z}.Finite := by
    apply Set.Finite.of_finite_image (f := fun z => Finset.univ.filter (fun i => z i = 0))
    · exact Set.toFinite _
    · intro z hz z' hz' heq
      simp only at heq
      have hw : z - z' = 0 := by
        apply hz.2
        · intro i hi
          have : i ∈ Finset.univ.filter (fun i => z' i = 0) := by
            rw [← heq]; simp [hi]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          simp [hi, this]
        · rw [map_sub, hz.1.2, hz'.1.2, sub_self]
      exact sub_eq_zero.mp hw
  obtain ⟨z0, hz00, hz0d⟩ := hne
  obtain ⟨g0, hg0, -⟩ := reduce _ z0 hz00 hz0d rfl
  obtain ⟨zs, hzs, hzsmin⟩ := Set.exists_min_image {z : ι → ℝ | Good z} (fun z => cc ⬝ᵥ z)
    hfin ⟨g0, hg0⟩
  refine ⟨zs, hzs.1, ?_⟩
  intro z' hz'0 hz'd
  obtain ⟨g, hg, hgcc⟩ := reduce _ z' hz'0 hz'd rfl
  exact (hzsmin g hg).trans hgcc

section Recourse

open StochasticProg.Recourse

theorem foldr_coe (l : List ℝ) :
    (l.map (fun r : ℝ => (r : EReal))).foldr bookAdd 0 = ((l.sum : ℝ) : EReal) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.foldr_cons, ih, List.sum_cons, bookAdd, if_neg (by simp),
      EReal.coe_add]

theorem foldr_top (l : List EReal) (h : ⊤ ∈ l) : l.foldr bookAdd 0 = ⊤ := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with h | h
    · simp [bookAdd, ← h]
    · simp [bookAdd, ih h]

theorem Q_eq {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ)
    (r : Fin K → ℝ) (hr : ∀ k, inst.p k ≠ 0 → QVal inst x k = (r k : EReal)) :
    Q inst x = ((∑ k, inst.p k * r k : ℝ) : EReal) := by
  have hl : List.ofFn (fun k : Fin K => (inst.p k : EReal) * QVal inst x k) =
      (List.ofFn (fun k => inst.p k * r k)).map (fun r : ℝ => (r : EReal)) := by
    rw [List.map_ofFn]
    congr 1
    funext k
    simp only [Function.comp_apply]
    by_cases hk : inst.p k = 0
    · simp [hk]
    · rw [hr k hk, ← EReal.coe_mul]
  unfold Q
  rw [hl, foldr_coe, List.sum_ofFn]

theorem QVal_ne_top {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ)
    (hx : Q inst x ≠ ⊤) (k : Fin K) (hk : inst.p k ≠ 0) : QVal inst x k ≠ ⊤ := by
  intro htop
  apply hx
  unfold Q
  apply foldr_top
  refine List.mem_ofFn.mpr ⟨k, ?_⟩
  rw [htop]
  exact EReal.coe_mul_top_of_pos (lt_of_le_of_ne (inst.hp_nonneg k) (Ne.symm hk))

theorem QVal_attain {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ)
    (k : Fin K) (hbot : QVal inst x k ≠ ⊥) (htop : QVal inst x k ≠ ⊤) :
    ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧ inst.W *ᵥ y = inst.h k - inst.T k *ᵥ x ∧
      QVal inst x k = ((inst.q k ⬝ᵥ y : ℝ) : EReal) := by
  set S := {z : EReal | ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
    Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x ∧
    z = ((dotProduct (inst.q k) y : ℝ) : EReal)} with hS
  have hQ : QVal inst x k = sInf S := rfl
  obtain ⟨r, hr⟩ : ∃ r : ℝ, QVal inst x k = r := ⟨_, (EReal.coe_toReal htop hbot).symm⟩
  have hSne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hQ, h, sInf_empty] at htop
    exact htop rfl
  obtain ⟨_, y0, hy00, hy0d, -⟩ := hSne
  obtain ⟨y, ⟨hy0, hyd⟩, hymin⟩ := lp_attain (Matrix.mulVecLin inst.W)
    (inst.h k - inst.T k *ᵥ x) (inst.q k) ⟨y0, hy00, by simpa using hy0d⟩ ⟨r, fun y hy0 hyd => by
      have : sInf S ≤ ((inst.q k ⬝ᵥ y : ℝ) : EReal) :=
        sInf_le ⟨y, hy0, by simpa using hyd, rfl⟩
      rw [← hQ, hr] at this
      exact EReal.coe_le_coe_iff.mp this⟩
  simp only [Matrix.mulVecLin_apply] at hyd hymin
  refine ⟨y, hy0, hyd, le_antisymm (sInf_le ⟨y, hy0, hyd, rfl⟩) ?_⟩
  rw [hQ]
  apply le_sInf
  rintro _ ⟨y', hy'0, hy'd, rfl⟩
  exact EReal.coe_le_coe_iff.mpr (hymin y' hy'0 hy'd)

end Recourse

end SolD74bda2c

open StochasticProg.Recourse Matrix in
theorem solution {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K)
    (hQ : ∀ x k, QVal inst x k ≠ ⊥)
    (hfin : ∃ z0 : ℝ, sInf (obj inst '' (K1 inst ∩ K2 inst)) = (z0 : EReal))
    (hcond :
      Bornology.IsBounded (K1 inst ∩ K2 inst) ∨
        ∃ rcQ : (Fin n1 → ℝ) → ℝ,
          ∀ x ∈ K1 inst ∩ K2 inst, ∀ v : Fin n1 → ℝ,
            (∀ lam : ℝ, 0 ≤ lam → x + lam • v ∈ K1 inst ∩ K2 inst) →
            ∃ lam0 : ℝ, 0 ≤ lam0 ∧
              ∀ lam : ℝ, lam0 ≤ lam →
                Q inst (x + lam • v) =
                  Q inst (x + lam0 • v) + (((lam - lam0) * rcQ v : ℝ) : EReal)) :
    ∃ x ∈ K1 inst ∩ K2 inst, obj inst x = sInf (obj inst '' (K1 inst ∩ K2 inst)) := by
  clear hcond
  obtain ⟨z0, hz0⟩ := hfin
  let xproj : (Fin n1 ⊕ (Fin K × Fin n2) → ℝ) →ₗ[ℝ] (Fin n1 → ℝ) :=
    LinearMap.funLeft ℝ ℝ Sum.inl
  let yproj : Fin K → (Fin n1 ⊕ (Fin K × Fin n2) → ℝ) →ₗ[ℝ] (Fin n2 → ℝ) := fun k =>
    LinearMap.funLeft ℝ ℝ (fun j : Fin n2 => (Sum.inr (k, j) : Fin n1 ⊕ (Fin K × Fin n2)))
  let L : (Fin n1 ⊕ (Fin K × Fin n2) → ℝ) →ₗ[ℝ]
      ((Fin m1 → ℝ) × ({k : Fin K // inst.p k ≠ 0} → Fin m2 → ℝ)) :=
    LinearMap.prod (inst.A.mulVecLin ∘ₗ xproj)
      (LinearMap.pi fun k : {k : Fin K // inst.p k ≠ 0} =>
        inst.W.mulVecLin ∘ₗ yproj k.1 + (inst.T k.1).mulVecLin ∘ₗ xproj)
  let d : (Fin m1 → ℝ) × ({k : Fin K // inst.p k ≠ 0} → Fin m2 → ℝ) :=
    (inst.b, fun k => inst.h k.1)
  let cc : Fin n1 ⊕ (Fin K × Fin n2) → ℝ :=
    Sum.elim inst.c (fun kj => inst.p kj.1 * inst.q kj.1 kj.2)
  have hL : ∀ z, L z = d ↔ inst.A *ᵥ (fun i => z (Sum.inl i)) = inst.b ∧
      ∀ k, inst.p k ≠ 0 → inst.W *ᵥ (fun j => z (Sum.inr (k, j))) =
        inst.h k - inst.T k *ᵥ (fun i => z (Sum.inl i)) := by
    intro z
    have hLz : L z = (inst.A *ᵥ (fun i => z (Sum.inl i)), fun k : {k : Fin K // inst.p k ≠ 0} =>
        inst.W *ᵥ (fun j => z (Sum.inr (k.1, j))) + inst.T k.1 *ᵥ (fun i => z (Sum.inl i))) := rfl
    rw [hLz, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun k hk => ?_⟩
      have := congrFun h2 ⟨k, hk⟩
      exact eq_sub_of_add_eq this
    · rintro ⟨h1, h2⟩
      refine ⟨h1, funext fun k => ?_⟩
      show _ = inst.h k.1
      rw [h2 k.1 k.2, sub_add_cancel]
  have hcc : ∀ z, cc ⬝ᵥ z = inst.c ⬝ᵥ (fun i => z (Sum.inl i)) +
      ∑ k, inst.p k * (inst.q k ⬝ᵥ (fun j => z (Sum.inr (k, j)))) := by
    intro z
    simp only [cc, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
  -- Step A: LP-feasible points give feasible first-stage points with no larger objective
  have stepA : ∀ z, (∀ i, 0 ≤ z i) → L z = d →
      (fun i => z (Sum.inl i)) ∈ K1 inst ∩ K2 inst ∧
        obj inst (fun i => z (Sum.inl i)) ≤ ((cc ⬝ᵥ z : ℝ) : EReal) := by
    intro z hz hzd
    obtain ⟨hA, hsc⟩ := (hL z).mp hzd
    set x : Fin n1 → ℝ := fun i => z (Sum.inl i) with hx
    have hle : ∀ k, inst.p k ≠ 0 →
        QVal inst x k ≤ ((inst.q k ⬝ᵥ (fun j => z (Sum.inr (k, j))) : ℝ) : EReal) := by
      intro k hk
      exact sInf_le ⟨_, fun j => hz _, hsc k hk, rfl⟩
    have hr : ∀ k, inst.p k ≠ 0 → QVal inst x k = (((QVal inst x k).toReal : ℝ) : EReal) := by
      intro k hk
      exact (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hle k hk))
        (hQ x k)).symm
    have hQx := SolD74bda2c.Q_eq inst x _ hr
    refine ⟨⟨⟨hA, fun i => hz _⟩, ?_⟩, ?_⟩
    · show Q inst x ≠ ⊤
      rw [hQx]; exact EReal.coe_ne_top _
    · show ((inst.c ⬝ᵥ x : ℝ) : EReal) + Q inst x ≤ _
      rw [hQx, ← EReal.coe_add, EReal.coe_le_coe_iff, hcc]
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : inst.p k = 0
      · simp [hk]
      · apply mul_le_mul_of_nonneg_left _ (inst.hp_nonneg k)
        have := hle k hk
        rw [hr k hk] at this
        exact EReal.coe_le_coe_iff.mp this
  -- Step B: every feasible first-stage point lifts to an LP-feasible point of equal cost
  have stepB : ∀ x ∈ K1 inst ∩ K2 inst, ∃ z, (∀ i, 0 ≤ z i) ∧ L z = d ∧
      ((cc ⬝ᵥ z : ℝ) : EReal) = obj inst x := by
    intro x hx
    have hy : ∀ k, ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧ (inst.p k ≠ 0 →
        inst.W *ᵥ y = inst.h k - inst.T k *ᵥ x ∧ QVal inst x k = ((inst.q k ⬝ᵥ y : ℝ) : EReal)) := by
      intro k
      by_cases hk : inst.p k = 0
      · exact ⟨0, fun _ => le_rfl, fun h => absurd hk h⟩
      · obtain ⟨y, hy0, hyd, hyv⟩ := SolD74bda2c.QVal_attain inst x k (hQ x k) (SolD74bda2c.QVal_ne_top inst x hx.2 k hk)
        exact ⟨y, hy0, fun _ => ⟨hyd, hyv⟩⟩
    choose y hy0 hy using hy
    refine ⟨Sum.elim x (fun kj => y kj.1 kj.2), ?_, ?_, ?_⟩
    · rintro (i | ⟨k, j⟩)
      · exact hx.1.2 i
      · exact hy0 k j
    · rw [hL]
      exact ⟨hx.1.1, fun k hk => (hy k hk).1⟩
    · rw [hcc]
      have hQx := SolD74bda2c.Q_eq inst x (fun k => inst.q k ⬝ᵥ y k) (fun k hk => (hy k hk).2)
      show _ = ((inst.c ⬝ᵥ x : ℝ) : EReal) + Q inst x
      rw [hQx, ← EReal.coe_add]
      rfl
  -- nonemptiness of the feasible region
  have hFne : (K1 inst ∩ K2 inst).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.image_empty, sInf_empty] at hz0
    exact EReal.coe_ne_top z0 hz0.symm
  obtain ⟨x0, hx0⟩ := hFne
  obtain ⟨z1, hz10, hz1d, -⟩ := stepB x0 hx0
  obtain ⟨zs, ⟨hzs0, hzsd⟩, hzsmin⟩ := SolD74bda2c.lp_attain L d cc ⟨z1, hz10, hz1d⟩ ⟨z0, fun z hz hzd => by
    obtain ⟨hmem, hle⟩ := stepA z hz hzd
    have h1 : sInf (obj inst '' (K1 inst ∩ K2 inst)) ≤ obj inst (fun i => z (Sum.inl i)) :=
      sInf_le (Set.mem_image_of_mem _ hmem)
    rw [hz0] at h1
    exact EReal.coe_le_coe_iff.mp (h1.trans hle)⟩
  obtain ⟨hmem, hle⟩ := stepA zs hzs0 hzsd
  refine ⟨_, hmem, le_antisymm ?_ (sInf_le (Set.mem_image_of_mem _ hmem))⟩
  apply le_sInf
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz, hzd, hzv⟩ := stepB x hx
  rw [← hzv]
  exact hle.trans (EReal.coe_le_coe_iff.mpr (hzsmin z hz hzd))
