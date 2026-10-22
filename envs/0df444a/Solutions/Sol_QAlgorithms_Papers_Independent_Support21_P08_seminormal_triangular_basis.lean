-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P08.seminormal_triangular_basis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:17:43.847996+00:00
-- url     : https://prove2.me/submissions/7a6a5a09-c788-4411-bdb2-5488cb1c2490

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section SeparatedDefinitions

variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

omit [Fintype Shape] [∀ l, Fintype (T l)] in
theorem g67d_td_refl (x : CellTableau Shape T) : tabDominates x x :=
  Or.inr ⟨x.1, x.2, x.2, rfl, rfl, le_rfl⟩

omit [Fintype Shape] [∀ l, Fintype (T l)] in
theorem g67d_td_fst {x y : CellTableau Shape T} (h : tabDominates x y) : y.1 ≤ x.1 := by
  rcases h with h | ⟨l, s, t, rfl, rfl, _⟩
  · exact h.le
  · exact le_rfl

omit [Fintype Shape] [∀ l, Fintype (T l)] in
theorem g67d_td_trans {x y z : CellTableau Shape T} (h1 : tabDominates x y)
    (h2 : tabDominates y z) : tabDominates x z := by
  rcases h1 with h1 | ⟨l, s, t, rfl, rfl, h1⟩
  · exact Or.inl (lt_of_le_of_lt (g67d_td_fst h2) h1)
  · rcases h2 with h2 | ⟨l', s', t', h3, rfl, h2⟩
    · exact Or.inl h2
    · obtain ⟨rfl, h4⟩ := Sigma.mk.inj_iff.mp h3
      have := eq_of_heq h4
      subst this
      exact Or.inr ⟨l, s, t', rfl, rfl, le_trans h2 h1⟩

omit [Fintype Shape] [∀ l, Fintype (T l)] in
theorem g67d_td_antisymm {x y : CellTableau Shape T} (h1 : tabDominates x y)
    (h2 : tabDominates y x) : x = y := by
  rcases h1 with h1 | ⟨l, s, t, rfl, rfl, h1⟩
  · exact absurd (lt_of_lt_of_le h1 (g67d_td_fst h2)) (lt_irrefl _)
  · rcases h2 with h2 | ⟨l', s', t', h3, h5, h2⟩
    · exact absurd h2 (lt_irrefl _)
    · obtain ⟨rfl, h4⟩ := Sigma.mk.inj_iff.mp h3
      obtain ⟨-, h6⟩ := Sigma.mk.inj_iff.mp h5
      have e1 := eq_of_heq h4
      have e2 := eq_of_heq h6
      subst e1 e2
      rw [le_antisymm h1 h2]

omit [Fintype Shape] [∀ l, Fintype (T l)] in
theorem g67d_idx_ext {x y : CellIndex Shape T} (h1 : (⟨x.1, x.2.1⟩ : CellTableau Shape T) = ⟨y.1, y.2.1⟩)
    (h2 : (⟨x.1, x.2.2⟩ : CellTableau Shape T) = ⟨y.1, y.2.2⟩) : x = y := by
  obtain ⟨l, s, t⟩ := x
  obtain ⟨m, u, v⟩ := y
  obtain ⟨rfl, e1⟩ := Sigma.mk.inj_iff.mp h1
  obtain ⟨-, e2⟩ := Sigma.mk.inj_iff.mp h2
  have := eq_of_heq e1; have := eq_of_heq e2
  subst_vars; rfl

omit [Fintype Shape] [∀ l, Fintype (T l)] in
theorem g67d_pd_trans {x y z : CellIndex Shape T} (h1 : pairDominates x y)
    (h2 : pairDominates y z) : pairDominates x z := by
  refine ⟨g67d_td_trans h1.1 h2.1, g67d_td_trans h1.2.1 h2.2.1, ?_⟩
  rintro rfl
  apply h2.2.2
  exact g67d_idx_ext (g67d_td_antisymm h2.1 (h1.1)) (g67d_td_antisymm h2.2.1 h1.2.1)

omit [Fintype Shape] [∀ l, Fintype (T l)] in
theorem g67d_pd_irrefl (x : CellIndex Shape T) : ¬ pairDominates x x := fun h => h.2.2 rfl

/-- transpose of an index -/
def g67d_tr (x : CellIndex Shape T) : CellIndex Shape T := ⟨x.1, (x.2.2, x.2.1)⟩

omit [Fintype Shape] [∀ l, Fintype (T l)] in
theorem g67d_pd_tr {x y : CellIndex Shape T} (h : pairDominates x y) :
    pairDominates (g67d_tr x) (g67d_tr y) := by
  refine ⟨h.2.1, h.1, ?_⟩
  intro he
  apply h.2.2
  obtain ⟨l, s, t⟩ := x
  obtain ⟨m, u, v⟩ := y
  simp only [g67d_tr] at he
  obtain ⟨rfl, e⟩ := Sigma.mk.inj_iff.mp he
  have := eq_of_heq e
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  rfl

/-- span of strictly dominating basis vectors -/
def g67d_Up (D : CellDatum (R := K) (A := A) (T := T)) (z : CellIndex Shape T) : Submodule K A :=
  Submodule.span K {x | ∃ w, pairDominates w z ∧ x = D.basis w}

theorem g67d_Up_mono {D : CellDatum (R := K) (A := A) (T := T)} {u z : CellIndex Shape T}
    (h : pairDominates u z) : g67d_Up D u ≤ g67d_Up D z := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  exact Submodule.subset_span ⟨w, g67d_pd_trans hw h, rfl⟩

theorem g67d_higher_le (D : CellDatum (R := K) (A := A) (T := T)) (l : Shape) (s t : T l) :
    higherSpan (R := K) D.basis l ≤ g67d_Up D ⟨l, (s, t)⟩ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨m, x, y, hlm, rfl⟩
  refine Submodule.subset_span ⟨⟨m, (x, y)⟩, ⟨Or.inl hlm, Or.inl hlm, ?_⟩, rfl⟩
  intro h
  have h' : m = l := congrArg Sigma.fst h
  rw [h'] at hlm
  exact lt_irrefl _ hlm

theorem g67d_right (J : JMFamily D M) (w : CellIndex Shape T) (i : Fin M) :
    D.basis w * J.L i - J.content ⟨w.1, w.2.2⟩ i • D.basis w ∈ g67d_Up D w := by
  obtain ⟨l, s, t⟩ := w
  obtain ⟨r, hr⟩ := J.triangular l t i
  have h := g67d_higher_le D l s t (hr s)
  have hsum : ∑ v ∈ Finset.univ.filter (fun v : T l => t < v), r v • D.basis ⟨l, (s, v)⟩ ∈
      g67d_Up D ⟨l, (s, t)⟩ := by
    refine Submodule.sum_mem _ (fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine ⟨⟨l, (s, v)⟩, ⟨g67d_td_refl _, Or.inr ⟨l, v, t, rfl, rfl, hv.le⟩, ?_⟩, rfl⟩
    intro he
    obtain ⟨-, e⟩ := Sigma.mk.inj_iff.mp he
    have := eq_of_heq e
    simp only [Prod.mk.injEq] at this
    exact absurd this.2 (ne_of_gt hv)
  have := Submodule.add_mem _ h hsum
  simpa using this

theorem g67d_star_Up (D : CellDatum (R := K) (A := A) (T := T)) (z : CellIndex Shape T) :
    ∀ x ∈ g67d_Up D (g67d_tr z), D.star x ∈ g67d_Up D z := by
  intro x hx
  have : g67d_Up D (g67d_tr z) ≤ (g67d_Up D z).comap D.star := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    show D.star (D.basis w) ∈ g67d_Up D z
    obtain ⟨l, s, t⟩ := w
    rw [D.star_basis]
    refine Submodule.subset_span ⟨⟨l, (t, s)⟩, ?_, rfl⟩
    have := g67d_pd_tr hw
    simpa [g67d_tr] using this
  exact this hx

theorem g67d_left (J : JMFamily D M) (w : CellIndex Shape T) (i : Fin M) :
    J.L i * D.basis w - J.content ⟨w.1, w.2.1⟩ i • D.basis w ∈ g67d_Up D w := by
  have h := g67d_right J (g67d_tr w) i
  have h2 := g67d_star_Up D w _ h
  obtain ⟨l, s, t⟩ := w
  simp only [g67d_tr] at h2
  rw [map_sub, map_smul, D.star_mul, J.fixed, D.star_basis] at h2
  exact h2

theorem g67d_Up_right (J : JMFamily D M) (z : CellIndex Shape T) :
    ∀ y ∈ jmAlgebra J, ∀ x ∈ g67d_Up D z, x * y ∈ g67d_Up D z := by
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    intro x hx
    have : g67d_Up D z ≤ (g67d_Up D z).comap (LinearMap.mulRight K (J.L i)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨w, hw, rfl⟩
      show D.basis w * J.L i ∈ g67d_Up D z
      have h1 := g67d_Up_mono hw (g67d_right J w i)
      have h2 : J.content ⟨w.1, w.2.2⟩ i • D.basis w ∈ g67d_Up D z :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, hw, rfl⟩)
      simpa using Submodule.add_mem _ h1 h2
    exact this hx
  | algebraMap r =>
    intro x hx
    rw [← Algebra.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ _ hx
  | add y1 y2 _ _ h1 h2 =>
    intro x hx; rw [mul_add]; exact Submodule.add_mem _ (h1 x hx) (h2 x hx)
  | mul y1 y2 _ _ h1 h2 =>
    intro x hx; rw [← mul_assoc]; exact h2 _ (h1 x hx)

theorem g67d_Up_left (J : JMFamily D M) (z : CellIndex Shape T) :
    ∀ y ∈ jmAlgebra J, ∀ x ∈ g67d_Up D z, y * x ∈ g67d_Up D z := by
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    intro x hx
    have : g67d_Up D z ≤ (g67d_Up D z).comap (LinearMap.mulLeft K (J.L i)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨w, hw, rfl⟩
      show J.L i * D.basis w ∈ g67d_Up D z
      have h1 := g67d_Up_mono hw (g67d_left J w i)
      have h2 : J.content ⟨w.1, w.2.1⟩ i • D.basis w ∈ g67d_Up D z :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, hw, rfl⟩)
      simpa using Submodule.add_mem _ h1 h2
    exact this hx
  | algebraMap r =>
    intro x hx
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ _ hx
  | add y1 y2 _ _ h1 h2 =>
    intro x hx; rw [add_mul]; exact Submodule.add_mem _ (h1 x hx) (h2 x hx)
  | mul y1 y2 _ _ h1 h2 =>
    intro x hx; rw [mul_assoc]; exact h1 _ (h2 x hx)

/-- the factor list of `jmSpectralProjector` -/
theorem g67d_proj_eq (J : JMFamily D M) (t : CellTableau Shape T) :
    jmSpectralProjector J t = (List.ofFn (fun i : Fin M =>
      (((contents J i).erase (J.content t i)).toList.map (fun c =>
        (J.content t i - c)⁻¹ • (J.L i - algebraMap K A c))).prod)).prod := by
  unfold jmSpectralProjector; congr

theorem g67d_proj_ind (J : JMFamily D M) (t : CellTableau Shape T) (p : A → Prop)
    (hmul : ∀ a b, p a → p b → p (a * b)) (h1 : p 1)
    (hf : ∀ i c, c ≠ J.content t i → p ((J.content t i - c)⁻¹ • (J.L i - algebraMap K A c))) :
    p (jmSpectralProjector J t) := by
  rw [g67d_proj_eq]
  refine List.prod_induction p hmul h1 (fun x hx => ?_)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  refine List.prod_induction p hmul h1 (fun y hy => ?_)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
  rw [Finset.mem_toList] at hc
  exact hf i c (Finset.ne_of_mem_erase hc)

theorem g67d_proj_mem (J : JMFamily D M) (t : CellTableau Shape T) :
    jmSpectralProjector J t ∈ jmAlgebra J := by
  refine g67d_proj_ind J t (· ∈ jmAlgebra J) (fun a b ha hb => Subalgebra.mul_mem _ ha hb)
    (Subalgebra.one_mem _) (fun i c _ => ?_)
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_range_self i))
    (Subalgebra.algebraMap_mem _ _)) _

theorem g67d_lead_right (J : JMFamily D M) (z : CellIndex Shape T) :
    D.basis z * jmSpectralProjector J ⟨z.1, z.2.2⟩ - D.basis z ∈ g67d_Up D z := by
  have := g67d_proj_ind J ⟨z.1, z.2.2⟩
    (fun y => y ∈ jmAlgebra J ∧ D.basis z * y - D.basis z ∈ g67d_Up D z)
    (fun a b ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨Subalgebra.mul_mem _ ha hb, by
      have e : D.basis z * (a * b) - D.basis z =
          (D.basis z * a - D.basis z) * b + (D.basis z * b - D.basis z) := by noncomm_ring
      rw [e]
      exact Submodule.add_mem _ (g67d_Up_right J z b hb _ ha') hb'⟩)
    ⟨Subalgebra.one_mem _, by simp⟩
    (fun i c hc => ⟨Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_range_self i))
      (Subalgebra.algebraMap_mem _ _)) _, by
        have hr := g67d_right J z i
        have hne : J.content ⟨z.1, z.2.2⟩ i - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
        have e : D.basis z * ((J.content ⟨z.1, z.2.2⟩ i - c)⁻¹ • (J.L i - algebraMap K A c)) -
            D.basis z = (J.content ⟨z.1, z.2.2⟩ i - c)⁻¹ •
              (D.basis z * J.L i - J.content ⟨z.1, z.2.2⟩ i • D.basis z) := by
          rw [mul_smul_comm, mul_sub, ← Algebra.commutes, ← Algebra.smul_def, smul_sub, smul_sub,
            smul_smul, smul_smul]
          have hk : (J.content ⟨z.1, z.2.2⟩ i - c)⁻¹ * J.content ⟨z.1, z.2.2⟩ i =
              (J.content ⟨z.1, z.2.2⟩ i - c)⁻¹ * c + 1 := by
            have := inv_mul_cancel₀ hne
            linear_combination this
          rw [hk, add_smul, one_smul]
          abel
        rw [e]
        exact Submodule.smul_mem _ _ hr⟩)
  exact this.2

theorem g67d_lead_left (J : JMFamily D M) (z : CellIndex Shape T) :
    jmSpectralProjector J ⟨z.1, z.2.1⟩ * D.basis z - D.basis z ∈ g67d_Up D z := by
  have := g67d_proj_ind J ⟨z.1, z.2.1⟩
    (fun y => y ∈ jmAlgebra J ∧ y * D.basis z - D.basis z ∈ g67d_Up D z)
    (fun a b ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨Subalgebra.mul_mem _ ha hb, by
      have e : a * b * D.basis z - D.basis z =
          a * (b * D.basis z - D.basis z) + (a * D.basis z - D.basis z) := by noncomm_ring
      rw [e]
      exact Submodule.add_mem _ (g67d_Up_left J z a ha _ hb') ha'⟩)
    ⟨Subalgebra.one_mem _, by simp⟩
    (fun i c hc => ⟨Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_range_self i))
      (Subalgebra.algebraMap_mem _ _)) _, by
        have hr := g67d_left J z i
        have hne : J.content ⟨z.1, z.2.1⟩ i - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
        have e : (J.content ⟨z.1, z.2.1⟩ i - c)⁻¹ • (J.L i - algebraMap K A c) * D.basis z -
            D.basis z = (J.content ⟨z.1, z.2.1⟩ i - c)⁻¹ •
              (J.L i * D.basis z - J.content ⟨z.1, z.2.1⟩ i • D.basis z) := by
          rw [smul_mul_assoc, sub_mul, ← Algebra.smul_def, smul_sub, smul_sub,
            smul_smul, smul_smul]
          have hk : (J.content ⟨z.1, z.2.1⟩ i - c)⁻¹ * J.content ⟨z.1, z.2.1⟩ i =
              (J.content ⟨z.1, z.2.1⟩ i - c)⁻¹ * c + 1 := by
            have := inv_mul_cancel₀ hne
            linear_combination this
          rw [hk, add_smul, one_smul]
          abel
        rw [e]
        exact Submodule.smul_mem _ _ hr⟩)
  exact this.2

theorem g67d_semi_sub (J : JMFamily D M) (z : CellIndex Shape T) :
    seminormal J z - D.basis z ∈ g67d_Up D z := by
  unfold seminormal
  have h1 := g67d_lead_right J z
  have h2 := g67d_lead_left J z
  have e : jmSpectralProjector J ⟨z.1, z.2.1⟩ * D.basis z * jmSpectralProjector J ⟨z.1, z.2.2⟩ -
      D.basis z = jmSpectralProjector J ⟨z.1, z.2.1⟩ *
        (D.basis z * jmSpectralProjector J ⟨z.1, z.2.2⟩ - D.basis z) +
        (jmSpectralProjector J ⟨z.1, z.2.1⟩ * D.basis z - D.basis z) := by noncomm_ring
  rw [e]
  exact Submodule.add_mem _ (g67d_Up_left J z _ (g67d_proj_mem J _) _ h1) h2

theorem g67d_Up_repr {D : CellDatum (R := K) (A := A) (T := T)} (z : CellIndex Shape T) :
    ∀ x ∈ g67d_Up D z, ∀ w, ¬ pairDominates w z → D.basis.repr x w = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    intro w hw
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg]
    rintro rfl; exact hw hu
  | zero => intro w _; simp
  | add x y _ _ hx hy => intro w hw; simp [hx w hw, hy w hw]
  | smul r x _ hx => intro w hw; simp [hx w hw]

theorem g67d_Up_sum {D : CellDatum (R := K) (A := A) (T := T)} (z : CellIndex Shape T)
    (x : A) (hx : x ∈ g67d_Up D z) :
    x = ∑ w ∈ Finset.univ.filter (fun w => pairDominates w z), D.basis.repr x w • D.basis w := by
  conv_lhs => rw [← D.basis.sum_repr x]
  rw [Finset.sum_filter_of_ne]
  intro w _ hw
  by_contra h
  exact hw (by rw [g67d_Up_repr z x hx w h, zero_smul])

theorem g67d_jm_comm (J : JMFamily D M) {x y : A} (hx : x ∈ jmAlgebra J) (hy : y ∈ jmAlgebra J) :
    x * y = y * x := by
  have : Commute x y := by
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy (fun b hb => ?_)
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx (fun c hc => ?_)).symm
    obtain ⟨i, rfl⟩ := hb
    obtain ⟨j, rfl⟩ := hc
    exact J.commuting i j
  exact this.eq

theorem g67d_star_one (D : CellDatum (R := K) (A := A) (T := T)) : D.star 1 = 1 := by
  have h := D.star_mul (D.star 1) 1
  rw [mul_one, D.star_involutive 1, mul_one] at h
  exact h.symm

theorem g67d_star_jm (J : JMFamily D M) : ∀ y ∈ jmAlgebra J, D.star y = y := by
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact J.fixed i
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, g67d_star_one]
  | add y1 y2 _ _ h1 h2 => rw [map_add, h1, h2]
  | mul y1 y2 hy1 hy2 h1 h2 => rw [D.star_mul, h1, h2, g67d_jm_comm J hy2 hy1]

theorem g67d_rank_lt {x y : CellIndex Shape T} (h : pairDominates x y) :
    (Finset.univ.filter (fun u => pairDominates y u)).card <
      (Finset.univ.filter (fun u => pairDominates x u)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨y, by simp [h], by simp [g67d_pd_irrefl]⟩
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact g67d_pd_trans h hu

theorem solution (J : JMFamily D M)
    (hsep : separatesComparable J) :
    (∀ z : CellIndex Shape T, ∃ b : CellIndex Shape T → K,
      seminormal J z = D.basis z +
        ∑ w ∈ Finset.univ.filter (fun w => pairDominates w z), b w • D.basis w) ∧
    (∃ b : Module.Basis (CellIndex Shape T) K A, ∀ z, b z = seminormal J z) ∧
    (∀ l (s t : T l), D.star (seminormal J ⟨l, (s, t)⟩) =
      seminormal J ⟨l, (t, s)⟩) := by
  refine ⟨fun z => ⟨fun w => D.basis.repr (seminormal J z - D.basis z) w, ?_⟩, ?_, ?_⟩
  · have := g67d_Up_sum z _ (g67d_semi_sub J z)
    rw [← this]; abel
  · have hli : LinearIndependent K (seminormal J) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      by_contra hne
      push_neg at hne
      obtain ⟨z0, hz0⟩ := hne
      obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun y => g y ≠ 0))
        (fun y => (Finset.univ.filter (fun u => pairDominates y u)).card) ⟨z0, by simp [hz0]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hmin
      have hc := congrArg (fun x => D.basis.repr x z) hg
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
        smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hc
      have hterm : ∀ y, g y * D.basis.repr (seminormal J y) z = if y = z then g z else 0 := by
        intro y
        have e : D.basis.repr (seminormal J y) z =
            D.basis.repr (D.basis y) z + D.basis.repr (seminormal J y - D.basis y) z := by
          rw [map_sub]; simp
        rw [e, Module.Basis.repr_self, Finsupp.single_apply]
        by_cases hyz : y = z
        · subst hyz
          rw [g67d_Up_repr y _ (g67d_semi_sub J y) y (g67d_pd_irrefl y)]
          simp
        · rw [if_neg hyz, if_neg hyz, zero_add]
          by_cases hgy : g y = 0
          · rw [hgy, zero_mul]
          by_cases hp : pairDominates z y
          · have := hmin y hgy
            have := g67d_rank_lt hp
            omega
          · rw [g67d_Up_repr y _ (g67d_semi_sub J y) z hp, mul_zero]
      simp_rw [hterm] at hc
      simp at hc
      exact hz hc
    haveI : FiniteDimensional K A := Module.Finite.of_basis D.basis
    refine ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli
      (Module.finrank_eq_card_basis D.basis).symm, fun z => ?_⟩
    simp
  · intro l s t
    unfold seminormal
    rw [D.star_mul, D.star_mul, g67d_star_jm J _ (g67d_proj_mem J _),
      g67d_star_jm J _ (g67d_proj_mem J _), D.star_basis, mul_assoc]

end SeparatedDefinitions

end
