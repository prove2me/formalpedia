-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P08.symmetric_jm_central
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:51:32.070148+00:00
-- url     : https://prove2.me/submissions/58e10894-d1d7-443f-84c1-335f93ea3e37

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section G67EJ
variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

def g67e_prec (z w : CellIndex Shape T) : Prop :=
  z.1 < w.1 ∨ ∃ v : T z.1, z.2.2 < v ∧ w = ⟨z.1, (z.2.1, v)⟩

omit [Fintype Shape] [∀ l, Fintype (T l)] in
lemma g67e_prec_irrefl (z : CellIndex Shape T) : ¬ g67e_prec z z := by
  rintro (h | ⟨v, hv, h⟩)
  · exact lt_irrefl _ h
  · rcases z with ⟨l, s, t⟩
    simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
    subst h; exact lt_irrefl _ hv

omit [Fintype Shape] [∀ l, Fintype (T l)] in
lemma g67e_prec_trans {z w u : CellIndex Shape T} (h1 : g67e_prec z w) (h2 : g67e_prec w u) :
    g67e_prec z u := by
  rcases h1 with h1 | ⟨v, hv, rfl⟩
  · rcases h2 with h2 | ⟨v', hv', rfl⟩
    · exact Or.inl (lt_trans h1 h2)
    · exact Or.inl h1
  · rcases h2 with h2 | ⟨v', hv', rfl⟩
    · exact Or.inl h2
    · exact Or.inr ⟨v', lt_trans hv hv', rfl⟩

variable (D) in
def g67e_Gt (z : CellIndex Shape T) : Submodule K A :=
  Submodule.span K {x | ∃ w, g67e_prec z w ∧ x = D.basis w}

lemma g67e_repr_zero (z : CellIndex Shape T) (x : A) (hx : x ∈ g67e_Gt D z) :
    D.basis.repr x z = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨w, hw, rfl⟩
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg]
    rintro rfl; exact g67e_prec_irrefl w hw
  · simp
  · intro x y _ _ hx hy; simp [hx, hy]
  · intro c x _ hx; simp [hx]

lemma g67e_Gt_mono {z w : CellIndex Shape T} (h : g67e_prec z w) : g67e_Gt D w ≤ g67e_Gt D z := by
  apply Submodule.span_mono
  rintro _ ⟨u, hu, rfl⟩; exact ⟨u, g67e_prec_trans h hu, rfl⟩

lemma g67e_higher_le (z : CellIndex Shape T) : higherSpan (R := K) D.basis z.1 ≤ g67e_Gt D z := by
  apply Submodule.span_mono
  rintro _ ⟨m, s, t, hm, rfl⟩; exact ⟨⟨m, (s, t)⟩, Or.inl hm, rfl⟩

variable (D) in
def g67e_good (y : A) : Prop := ∀ z, ∃ c : K, D.basis z * y - c • D.basis z ∈ g67e_Gt D z

variable (D) in
def g67e_phi (z : CellIndex Shape T) (x : A) : K := D.basis.repr (D.basis z * x) z

lemma g67e_coef (y : A) (z : CellIndex Shape T) (c : K)
    (h : D.basis z * y - c • D.basis z ∈ g67e_Gt D z) : g67e_phi D z y = c := by
  have := g67e_repr_zero z _ h
  rw [map_sub, map_smul, Module.Basis.repr_self] at this
  simp only [Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at this
  unfold g67e_phi; linear_combination this

lemma g67e_Gt_stable (y : A) (hy : g67e_good D y) (z : CellIndex Shape T) (x : A)
    (hx : x ∈ g67e_Gt D z) : x * y ∈ g67e_Gt D z := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨c, hc⟩ := hy w
    have : D.basis w * y = c • D.basis w + (D.basis w * y - c • D.basis w) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, hw, rfl⟩))
      (g67e_Gt_mono hw hc)
  · simp
  · intro a b _ _ ha hb; rw [add_mul]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

variable (D) in
def g67e_T : Subalgebra K A :=
  { carrier := {y | g67e_good D y}
    mul_mem' := by
      intro y1 y2 h1 h2 z
      obtain ⟨c1, hc1⟩ := h1 z
      obtain ⟨c2, hc2⟩ := h2 z
      refine ⟨c1 * c2, ?_⟩
      have : D.basis z * (y1 * y2) - (c1 * c2) • D.basis z =
          (D.basis z * y1 - c1 • D.basis z) * y2 + c1 • (D.basis z * y2 - c2 • D.basis z) := by
        simp only [sub_mul, smul_sub, smul_mul_assoc, mul_assoc, mul_smul]; abel
      rw [this]
      exact Submodule.add_mem _ (g67e_Gt_stable y2 h2 z _ hc1) (Submodule.smul_mem _ _ hc2)
    add_mem' := by
      intro y1 y2 h1 h2 z
      obtain ⟨c1, hc1⟩ := h1 z
      obtain ⟨c2, hc2⟩ := h2 z
      refine ⟨c1 + c2, ?_⟩
      have : D.basis z * (y1 + y2) - (c1 + c2) • D.basis z =
          (D.basis z * y1 - c1 • D.basis z) + (D.basis z * y2 - c2 • D.basis z) := by
        rw [mul_add, add_smul]; abel
      rw [this]; exact Submodule.add_mem _ hc1 hc2
    algebraMap_mem' := by
      intro r z
      refine ⟨r, ?_⟩
      rw [← Algebra.commutes, ← Algebra.smul_def, sub_self]; exact Submodule.zero_mem _ }

lemma g67e_L_spec (J : JMFamily D M) (i : Fin M) (z : CellIndex Shape T) :
    D.basis z * J.L i - J.content ⟨z.1, z.2.2⟩ i • D.basis z ∈ g67e_Gt D z := by
  rcases z with ⟨l, s, t⟩
  obtain ⟨r, hr⟩ := J.triangular l t i
  have h := hr s
  have : D.basis ⟨l, (s, t)⟩ * J.L i - J.content ⟨l, t⟩ i • D.basis ⟨l, (s, t)⟩ =
      (D.basis ⟨l, (s, t)⟩ * J.L i - J.content ⟨l, t⟩ i • D.basis ⟨l, (s, t)⟩ -
        ∑ v ∈ Finset.univ.filter (fun v : T l => t < v), r v • D.basis ⟨l, (s, v)⟩) +
      ∑ v ∈ Finset.univ.filter (fun v : T l => t < v), r v • D.basis ⟨l, (s, v)⟩ := by abel
  rw [this]
  refine Submodule.add_mem _ (g67e_higher_le ⟨l, (s, t)⟩ h) (Submodule.sum_mem _ ?_)
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨l, (s, v)⟩, Or.inr ⟨v, hv, rfl⟩, rfl⟩)

lemma g67e_jm_le (J : JMFamily D M) : jmAlgebra J ≤ g67e_T D := by
  unfold jmAlgebra
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩ z
  exact ⟨_, g67e_L_spec J i z⟩

lemma g67e_phi_mul (z : CellIndex Shape T) (x y : A) (hx : g67e_good D x) (hy : g67e_good D y) :
    g67e_phi D z (x * y) = g67e_phi D z x * g67e_phi D z y := by
  obtain ⟨c1, hc1⟩ := hx z
  obtain ⟨c2, hc2⟩ := hy z
  have hxy : g67e_good D (x * y) := (g67e_T D).mul_mem hx hy
  rw [g67e_coef x z c1 hc1, g67e_coef y z c2 hc2]
  apply g67e_coef
  have : D.basis z * (x * y) - (c1 * c2) • D.basis z =
      (D.basis z * x - c1 • D.basis z) * y + c1 • (D.basis z * y - c2 • D.basis z) := by
    simp only [sub_mul, smul_sub, smul_mul_assoc, mul_assoc, mul_smul]; abel
  rw [this]
  exact Submodule.add_mem _ (g67e_Gt_stable y hy z _ hc1) (Submodule.smul_mem _ _ hc2)

def g67e_chiZ (J : JMFamily D M) (z : CellIndex Shape T) : jmAlgebra J →ₐ[K] K where
  toFun b := g67e_phi D z b.1
  map_one' := by simp [g67e_phi]
  map_mul' a b := g67e_phi_mul z a.1 b.1 (g67e_jm_le J a.2) (g67e_jm_le J b.2)
  map_zero' := by simp [g67e_phi]
  map_add' a b := by simp [g67e_phi, mul_add]
  commutes' r := by
    simp only [g67e_phi, Subalgebra.coe_algebraMap]
    rw [← Algebra.commutes, ← Algebra.smul_def, map_smul, Module.Basis.repr_self]
    simp

lemma g67e_chiZ_apply (J : JMFamily D M) (z : CellIndex Shape T) (b : jmAlgebra J) :
    g67e_chiZ J z b = g67e_phi D z b.1 := rfl

lemma g67e_phi_row (l : Shape) (s t : T l) (x : A) :
    g67e_phi D ⟨l, (s, t)⟩ x = g67e_phi D ⟨l, (t, t)⟩ x := by
  obtain ⟨r, hr⟩ := D.multiplication l t x
  have key : ∀ s' : T l, g67e_phi D ⟨l, (s', t)⟩ x = r t := by
    intro s'
    have h0 := g67e_repr_zero _ _ (g67e_higher_le ⟨l, (s', t)⟩ (hr s'))
    rw [map_sub, map_sum] at h0
    simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_sub, Pi.sub_apply,
      Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
      Finsupp.single_apply, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h0
    unfold g67e_phi; linear_combination h0
  rw [key s, key t]


variable (T) in
def g67e_N : ℕ := Fintype.card (CellIndex Shape T)

def g67e_hsh (l : Shape) : ℕ := (Finset.univ.filter (· < l)).card
def g67e_pos {l : Shape} (t : T l) : ℕ := (Finset.univ.filter (· < t)).card

omit [∀ l, PartialOrder (T l)] [∀ l, Fintype (T l)] in
lemma g67e_hsh_lt {l m : Shape} (h : l < m) : g67e_hsh l < g67e_hsh m := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨l, by simp [h], by simp⟩
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact lt_trans hx h

omit [Fintype Shape] [PartialOrder Shape] in
lemma g67e_pos_lt {l : Shape} {s t : T l} (h : s < t) : g67e_pos s < g67e_pos t := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨s, by simp [h], by simp⟩
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact lt_trans hx h

omit [PartialOrder Shape] in
lemma g67e_pos_le {l : Shape} (t : T l) : g67e_pos t ≤ g67e_N T := by
  unfold g67e_pos g67e_N
  refine le_trans (Finset.card_le_univ _) ?_
  exact Fintype.card_le_of_injective (fun t : T l => (⟨l, (t, t)⟩ : CellIndex Shape T))
    (fun a b h => by simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h; exact h.1)

def g67e_r (z : CellIndex Shape T) : ℕ := g67e_hsh z.1 * (g67e_N T + 1) + g67e_pos z.2.2
def g67e_rank (z : CellIndex Shape T) : ℕ :=
  g67e_r z * g67e_N T + (Fintype.equivFin (CellIndex Shape T) z : ℕ)

lemma g67e_r_lt {z w : CellIndex Shape T} (h : g67e_prec z w) : g67e_r z < g67e_r w := by
  rcases h with h | ⟨v, hv, rfl⟩
  · have h1 := g67e_hsh_lt h
    have h2 := g67e_pos_le z.2.2
    unfold g67e_r
    have : (g67e_hsh z.1 + 1) * (g67e_N T + 1) ≤ g67e_hsh w.1 * (g67e_N T + 1) :=
      Nat.mul_le_mul_right _ h1
    nlinarith
  · unfold g67e_r
    have := g67e_pos_lt hv
    simp only
    omega

lemma g67e_rank_lt {z w : CellIndex Shape T} (h : g67e_prec z w) : g67e_rank z < g67e_rank w := by
  have h1 := g67e_r_lt h
  have h2 : (Fintype.equivFin (CellIndex Shape T) z : ℕ) < g67e_N T :=
    (Fintype.equivFin (CellIndex Shape T) z).isLt
  unfold g67e_rank
  have : (g67e_r z + 1) * g67e_N T ≤ g67e_r w * g67e_N T := Nat.mul_le_mul_right _ h1
  nlinarith

lemma g67e_rank_inj {z w : CellIndex Shape T} (h : g67e_rank z = g67e_rank w) : z = w := by
  have h2 : (Fintype.equivFin (CellIndex Shape T) z : ℕ) < g67e_N T :=
    (Fintype.equivFin (CellIndex Shape T) z).isLt
  have h3 : (Fintype.equivFin (CellIndex Shape T) w : ℕ) < g67e_N T :=
    (Fintype.equivFin (CellIndex Shape T) w).isLt
  unfold g67e_rank at h
  have e1 : (g67e_r z * g67e_N T + (Fintype.equivFin (CellIndex Shape T) z : ℕ)) % g67e_N T =
      (Fintype.equivFin (CellIndex Shape T) z : ℕ) := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  have e2 : (g67e_r w * g67e_N T + (Fintype.equivFin (CellIndex Shape T) w : ℕ)) % g67e_N T =
      (Fintype.equivFin (CellIndex Shape T) w : ℕ) := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h3]
  have : (Fintype.equivFin (CellIndex Shape T) z : ℕ) = (Fintype.equivFin (CellIndex Shape T) w : ℕ) := by
    rw [← e1, ← e2, h]
  exact (Fintype.equivFin _).injective (Fin.ext this)

variable (D) in
def g67e_G (n : ℕ) : Submodule K A :=
  Submodule.span K {x | ∃ w, n ≤ g67e_rank w ∧ x = D.basis w}

lemma g67e_step (n : ℕ) (y : A) (hy : g67e_good D y)
    (hz : ∀ w : CellIndex Shape T, g67e_rank w = n → g67e_phi D w y = 0)
    (x : A) (hx : x ∈ g67e_G D n) : x * y ∈ g67e_G D (n + 1) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨c, hc⟩ := hy w
    have hgt : g67e_Gt D w ≤ g67e_G D (n + 1) := by
      apply Submodule.span_mono
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨u, by have := g67e_rank_lt hu; omega, rfl⟩
    have : D.basis w * y = c • D.basis w + (D.basis w * y - c • D.basis w) := by abel
    rw [this]
    refine Submodule.add_mem _ ?_ (hgt hc)
    by_cases hn : g67e_rank w = n
    · rw [← g67e_coef y w c hc, hz w hn, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, by omega, rfl⟩)
  · simp
  · intro a b _ _ ha hb; rw [add_mul]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

lemma g67e_G0 : (1 : A) ∈ g67e_G D 0 := by
  have : Submodule.span K (Set.range D.basis) ≤ g67e_G D 0 :=
    Submodule.span_mono (by rintro _ ⟨w, rfl⟩; exact ⟨w, Nat.zero_le _, rfl⟩)
  rw [D.basis.span_eq] at this
  exact this Submodule.mem_top

lemma g67e_Gbig (x : A) (hx : x ∈ g67e_G D (Finset.univ.sup (g67e_rank (T := T)) + 1)) : x = 0 := by
  have : g67e_G D (Finset.univ.sup (g67e_rank (T := T)) + 1) = ⊥ := by
    unfold g67e_G
    rw [Submodule.span_eq_bot]
    rintro _ ⟨w, hw, rfl⟩
    have := Finset.le_sup (f := g67e_rank (T := T)) (Finset.mem_univ w)
    omega
  rw [this] at hx; exact (Submodule.mem_bot K).mp hx

theorem g67e_main (J : JMFamily D M) :
    (∀ a b : jmAlgebra J, a * b = b * a) ∧
    ∃ chi : CellTableau Shape T → (jmAlgebra J →ₐ[K] K),
      (∀ t i, chi t (jmGenerator J i) = J.content t i) ∧
      (∀ (V : Type*) [AddCommGroup V] [Module K V]
        (rho : jmAlgebra J →ₐ[K] Module.End K V),
        IrreducibleRepresentation rho →
        ∃ t : CellTableau Shape T, ∃ e : V ≃ₗ[K] K,
          ∀ a v, e (rho a v) = chi t a * e v) := by
  refine ⟨?_, fun t => g67e_chiZ J ⟨t.1, (t.2, t.2)⟩, ?_, ?_⟩
  · intro a b
    have : IsMulCommutative (Algebra.adjoin K (Set.range J.L)) :=
      Algebra.isMulCommutative_adjoin K (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact J.commuting i j)
    exact this.is_comm.comm a b
  · intro t i
    rw [g67e_chiZ_apply]
    exact g67e_coef _ _ _ (g67e_L_spec J i ⟨t.1, (t.2, t.2)⟩)
  intro V _ _ rho hirr
  obtain ⟨⟨v0, hv0⟩, hinv⟩ := hirr
  let U : CellIndex Shape T → Submodule K V := fun z =>
    Submodule.span K {v' | ∃ b : jmAlgebra J, g67e_chiZ J z b = 0 ∧ ∃ v, v' = rho b v}
  have hUinv : ∀ z, ∀ c : jmAlgebra J, ∀ v ∈ U z, rho c v ∈ U z := by
    intro z c v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨b, hb, u, rfl⟩
      refine Submodule.subset_span ⟨c * b, by rw [map_mul, hb, mul_zero], u, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    · simp
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro r x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx
  by_cases hex : ∃ z, U z = ⊥
  · obtain ⟨z, hz⟩ := hex
    have hker : ∀ b : jmAlgebra J, g67e_chiZ J z b = 0 → ∀ v, rho b v = 0 := by
      intro b hb v
      have : rho b v ∈ U z := Submodule.subset_span ⟨b, hb, v, rfl⟩
      rw [hz] at this; exact (Submodule.mem_bot K).mp this
    have hscal : ∀ a v, rho a v = g67e_chiZ J z a • v := by
      intro a v
      have h1 := hker (a - algebraMap K _ (g67e_chiZ J z a))
        (by rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]) v
      rw [map_sub, AlgHom.commutes, LinearMap.sub_apply, Module.algebraMap_end_apply,
        sub_eq_zero] at h1
      exact h1
    have htop : Submodule.span K {v0} = ⊤ := by
      rcases hinv (Submodule.span K {v0}) (by
        intro a v hv
        rw [hscal]; exact Submodule.smul_mem _ _ hv) with h | h
      · exfalso; apply hv0
        have : v0 ∈ Submodule.span K {v0} := Submodule.mem_span_singleton_self v0
        rw [h] at this; exact (Submodule.mem_bot K).mp this
      · exact h
    let e : V ≃ₗ[K] K :=
      ((LinearEquiv.toSpanNonzeroSingleton K V v0 hv0).trans
        (LinearEquiv.ofTop _ htop)).symm
    refine ⟨⟨z.1, z.2.2⟩, e, fun a v => ?_⟩
    rw [hscal, map_smul, smul_eq_mul]
    congr 1
    rcases z with ⟨l, s, t⟩
    rw [g67e_chiZ_apply, g67e_chiZ_apply, g67e_phi_row]
  · exfalso
    push Not at hex
    have hUtop : ∀ z, U z = ⊤ := fun z => (hinv (U z) (fun c v hv => hUinv z c v hv)).resolve_left (hex z)
    let Sp : ℕ → Submodule K V := fun n =>
      Submodule.span K {v' | ∃ y : jmAlgebra J, (∀ x ∈ g67e_G D n, x * y.1 = 0) ∧ ∃ u, v' = rho y u}
    set Bd := Finset.univ.sup (g67e_rank (T := T)) + 1
    have hmap : ∀ n, ∀ b : jmAlgebra J,
        (∀ w : CellIndex Shape T, g67e_rank w = n → g67e_phi D w b.1 = 0) →
        ∀ u ∈ Sp (n + 1), rho b u ∈ Sp n := by
      intro n b hb u hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
      · rintro _ ⟨y, hy, u', rfl⟩
        refine Submodule.subset_span ⟨b * y, fun x hx => ?_, u', ?_⟩
        · show x * (b.1 * y.1) = 0
          rw [← mul_assoc]
          exact hy _ (g67e_step n b.1 (g67e_jm_le J b.2) hb x hx)
        · rw [map_mul, Module.End.mul_apply]
      · simp
      · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
      · intro r x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx
    have hSp : ∀ k, Sp (Bd - k) = ⊤ := by
      intro k
      induction k with
      | zero =>
        rw [eq_top_iff]
        intro v _
        refine Submodule.subset_span ⟨1, fun x hx => ?_, v, by simp⟩
        rw [Nat.sub_zero] at hx
        rw [g67e_Gbig x hx, zero_mul]
      | succ k ih =>
        by_cases hk : Bd ≤ k
        · rw [show Bd - (k + 1) = Bd - k by omega]; exact ih
        set n := Bd - (k + 1) with hn
        have hn1 : Bd - k = n + 1 := by omega
        rw [hn1] at ih
        rw [eq_top_iff]
        intro v _
        by_cases hz : ∃ z : CellIndex Shape T, g67e_rank z = n
        · obtain ⟨z, hz⟩ := hz
          have hv : v ∈ U z := by rw [hUtop z]; trivial
          refine (Submodule.span_le.mpr ?_) hv
          rintro _ ⟨b, hb, u, rfl⟩
          refine hmap n b (fun w hw => ?_) u (by rw [ih]; trivial)
          rw [g67e_rank_inj (hw.trans hz.symm)]
          exact hb
        · push Not at hz
          have hv : v ∈ Sp (n + 1) := by rw [ih]; trivial
          refine (Submodule.span_le.mpr ?_) hv
          rintro _ ⟨y, hy, u, rfl⟩
          refine Submodule.subset_span ⟨y, fun x hx => hy x ?_, u, rfl⟩
          refine (Submodule.span_le.mpr ?_) hx
          rintro _ ⟨w, hw, rfl⟩
          exact Submodule.subset_span ⟨w, by have := hz w; omega, rfl⟩
    have h0 : Sp 0 = ⊤ := by
      have := hSp Bd; rwa [Nat.sub_self] at this
    have hbot : Sp 0 = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨y, hy, u, rfl⟩
      have h1 := hy 1 g67e_G0
      rw [one_mul] at h1
      have : y = 0 := Subtype.ext h1
      rw [this, map_zero, LinearMap.zero_apply]
    apply hv0
    have : v0 ∈ Sp 0 := by rw [h0]; trivial
    rw [hbot] at this; exact (Submodule.mem_bot K).mp this


lemma g67e_repr_zero' (z w : CellIndex Shape T) (hw : ¬ g67e_prec z w) (x : A)
    (hx : x ∈ g67e_Gt D z) : D.basis.repr x w = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨u, hu, rfl⟩
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg]
    rintro rfl; exact hw hu
  · simp
  · intro x y _ _ hx hy; simp [hx, hy]
  · intro c x _ hx; simp [hx]

lemma g67e_repr_good (x : A) (hx : g67e_good D x) (z w : CellIndex Shape T) (hwz : w ≠ z)
    (hnp : ¬ g67e_prec z w) : D.basis.repr (D.basis z * x) w = 0 := by
  obtain ⟨c, hc⟩ := hx z
  have h1 := g67e_repr_zero' z w hnp _ hc
  rw [map_sub, map_smul, Module.Basis.repr_self] at h1
  simp only [Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply,
    Finsupp.single_apply, if_neg hwz.symm, smul_zero, sub_zero] at h1
  exact h1

lemma g67e_expand (x y : A) (z w : CellIndex Shape T) :
    D.basis.repr (D.basis z * x * y) w =
      ∑ u, D.basis.repr (D.basis z * x) u * D.basis.repr (D.basis u * y) w := by
  conv_lhs => rw [← D.basis.sum_repr (D.basis z * x)]
  rw [Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]

lemma g67e_tab_ne {z w : CellIndex Shape T} (h : g67e_prec z w) :
    (⟨z.1, z.2.2⟩ : CellTableau Shape T) ≠ ⟨w.1, w.2.2⟩ := by
  rcases h with h | ⟨v, hv, rfl⟩
  · intro e; exact (ne_of_lt h) (congrArg (fun x : CellTableau Shape T => x.1) e)
  · intro e
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at e
    exact (ne_of_lt hv) e

lemma g67e_comm (J : JMFamily D M) (a b : jmAlgebra J) : a * b = b * a := by
  have : IsMulCommutative (Algebra.adjoin K (Set.range J.L)) :=
    Algebra.isMulCommutative_adjoin K (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact J.commuting i j)
  exact this.is_comm.comm a b

lemma g67e_ss (J : JMFamily D M) (hsep : separatesAll J) (y : A) (hy : y ∈ jmAlgebra J)
    (h0 : ∀ z, g67e_phi D z y = 0) : y = 0 := by
  have hgy : g67e_good D y := g67e_jm_le J hy
  have hcomm : ∀ i, y * J.L i = J.L i * y := by
    intro i
    have := g67e_comm J ⟨y, hy⟩ (jmGenerator J i)
    exact congrArg Subtype.val this
  set X : CellIndex Shape T → CellIndex Shape T → K := fun z w => D.basis.repr (D.basis z * y) w
    with hX
  have hXd : ∀ z, X z z = 0 := fun z => h0 z
  have hXnp : ∀ z w, w ≠ z → ¬ g67e_prec z w → X z w = 0 :=
    fun z w h1 h2 => g67e_repr_good y hgy z w h1 h2
  have main : ∀ k, ∀ z w : CellIndex Shape T, g67e_rank w - g67e_rank z = k → X z w = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro z w hk
      by_cases hwz : w = z
      · subst hwz; exact hXd w
      by_cases hp : g67e_prec z w
      swap
      · exact hXnp z w hwz hp
      have hzw := g67e_rank_lt hp
      have hne := g67e_tab_ne hp
      have : J.content ⟨z.1, z.2.2⟩ ≠ J.content ⟨w.1, w.2.2⟩ := fun e => hne (hsep e)
      obtain ⟨i, hi⟩ := Function.ne_iff.mp this
      set Lm : CellIndex Shape T → CellIndex Shape T → K :=
        fun a b => D.basis.repr (D.basis a * J.L i) b with hLm
      have hLgood : g67e_good D (J.L i) := fun a => ⟨_, g67e_L_spec J i a⟩
      have hLd : ∀ a, Lm a a = J.content ⟨a.1, a.2.2⟩ i :=
        fun a => g67e_coef _ _ _ (g67e_L_spec J i a)
      have hLnp : ∀ a b, b ≠ a → ¬ g67e_prec a b → Lm a b = 0 :=
        fun a b h1 h2 => g67e_repr_good _ hLgood a b h1 h2
      have hid : ∑ u, X z u * Lm u w = ∑ u, Lm z u * X u w := by
        rw [← g67e_expand, ← g67e_expand, mul_assoc, hcomm i, ← mul_assoc]
      rw [Finset.sum_eq_single w, Finset.sum_eq_single z] at hid
      · rw [hLd, hLd] at hid
        have : X z w * (J.content ⟨w.1, w.2.2⟩ i - J.content ⟨z.1, z.2.2⟩ i) = 0 := by
          linear_combination hid
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h).symm hi
      · intro u _ huz
        by_cases hzu : g67e_prec z u
        · by_cases huw : u = w
          · subst huw; rw [hXd, mul_zero]
          by_cases hpu : g67e_prec u w
          · have h1 := g67e_rank_lt hzu
            have h2 := g67e_rank_lt hpu
            rw [ih (g67e_rank w - g67e_rank u) (by omega) u w rfl, mul_zero]
          · rw [hXnp u w (Ne.symm huw) hpu, mul_zero]
        · rw [hLnp z u huz hzu, zero_mul]
      · simp
      · intro u _ huw
        by_cases hzu : g67e_prec z u
        · by_cases hpu : g67e_prec u w
          · have h1 := g67e_rank_lt hzu
            have h2 := g67e_rank_lt hpu
            rw [ih (g67e_rank u - g67e_rank z) (by omega) z u rfl, zero_mul]
          · rw [hLnp u w (Ne.symm huw) hpu, mul_zero]
        · by_cases huz : u = z
          · subst huz; rw [hXd, zero_mul]
          · rw [hXnp z u huz hzu, zero_mul]
      · simp
  have hrow : ∀ z, D.basis z * y = 0 := by
    intro z
    apply D.basis.repr.injective
    ext w
    rw [map_zero, Finsupp.zero_apply]
    exact main _ z w rfl
  have : (1 : A) * y = 0 := by
    rw [← D.basis.sum_repr 1, Finset.sum_mul]
    exact Finset.sum_eq_zero (fun z _ => by rw [smul_mul_assoc, hrow, smul_zero])
  rwa [one_mul] at this


def g67e_Fb (J : JMFamily D M) (t : CellTableau Shape T) : jmAlgebra J :=
  (List.ofFn (fun i : Fin M =>
    (((contents J i).erase (J.content t i)).toList.map (fun c =>
      (J.content t i - c)⁻¹ • (jmGenerator J i - algebraMap K (jmAlgebra J) c))).prod)).prod

lemma g67e_Fb_coe (J : JMFamily D M) (t : CellTableau Shape T) :
    ((g67e_Fb J t : jmAlgebra J) : A) = jmSpectralProjector J t := by
  have h : ((g67e_Fb J t : jmAlgebra J) : A) = (jmAlgebra J).val (g67e_Fb J t) := rfl
  rw [h, g67e_Fb, map_list_prod, List.map_ofFn]
  unfold jmSpectralProjector
  congr 1
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply, map_list_prod, List.map_map]
  congr 1

lemma g67e_chi_gen (J : JMFamily D M) (z : CellIndex Shape T) (i : Fin M) :
    g67e_chiZ J z (jmGenerator J i) = J.content ⟨z.1, z.2.2⟩ i :=
  g67e_coef _ _ _ (g67e_L_spec J i z)

lemma g67e_chi_Fb (J : JMFamily D M) (hsep : separatesAll J) (z : CellIndex Shape T) (t : CellTableau Shape T) :
    g67e_chiZ J z (g67e_Fb J t) = if (⟨z.1, z.2.2⟩ : CellTableau Shape T) = t then 1 else 0 := by
  rw [g67e_Fb, map_list_prod, List.map_ofFn]
  split_ifs with h
  · apply List.prod_eq_one
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    simp only [Function.comp_apply, map_list_prod, List.map_map]
    apply List.prod_eq_one
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    rw [Finset.mem_toList, Finset.mem_erase] at hc
    simp only [Function.comp_apply, map_smul, map_sub, AlgHom.commutes, g67e_chi_gen,
      Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul, h]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hc.1.symm)
  · by_cases hc : J.content ⟨z.1, z.2.2⟩ = J.content t
    · exact absurd (hsep hc) h
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
      apply List.prod_eq_zero
      refine List.mem_ofFn.mpr ⟨i, ?_⟩
      simp only [Function.comp_apply, map_list_prod, List.map_map]
      apply List.prod_eq_zero
      refine List.mem_map.mpr ⟨J.content ⟨z.1, z.2.2⟩ i, ?_, ?_⟩
      · rw [Finset.mem_toList, Finset.mem_erase]
        exact ⟨hi, Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
      · simp only [Function.comp_apply, map_smul, map_sub, AlgHom.commutes, g67e_chi_gen,
          Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul, sub_self, mul_zero]


lemma g67e_FL (J : JMFamily D M) (hsep : separatesAll J) (t : CellTableau Shape T) (i : Fin M) :
    jmSpectralProjector J t * J.L i = J.content t i • jmSpectralProjector J t := by
  let b : jmAlgebra J := g67e_Fb J t * jmGenerator J i - J.content t i • g67e_Fb J t
  have hb : (b : A) = jmSpectralProjector J t * J.L i - J.content t i • jmSpectralProjector J t := by
    simp only [b, Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_smul, g67e_Fb_coe]; rfl
  have := g67e_ss J hsep (b : A) b.2 (fun z => by
    rw [← g67e_chiZ_apply]
    simp only [b, map_sub, map_mul, map_smul, g67e_chi_Fb J hsep, g67e_chi_gen, smul_eq_mul]
    split_ifs with h
    · rw [h]; ring
    · ring)
  rw [hb, sub_eq_zero] at this; exact this

lemma g67e_FF (J : JMFamily D M) (hsep : separatesAll J) (t u : CellTableau Shape T) :
    jmSpectralProjector J t * jmSpectralProjector J u =
      if u = t then jmSpectralProjector J t else 0 := by
  let b : jmAlgebra J := g67e_Fb J t * g67e_Fb J u - if u = t then g67e_Fb J t else 0
  have hb : (b : A) = jmSpectralProjector J t * jmSpectralProjector J u -
      if u = t then jmSpectralProjector J t else 0 := by
    simp only [b, Subalgebra.coe_sub, Subalgebra.coe_mul, g67e_Fb_coe]
    split_ifs <;> simp [g67e_Fb_coe]
  have := g67e_ss J hsep (b : A) b.2 (fun z => by
    rw [← g67e_chiZ_apply]
    simp only [b, map_sub, map_mul, g67e_chi_Fb J hsep]
    by_cases hut : u = t
    · subst hut; rw [if_pos rfl, g67e_chi_Fb J hsep]; split_ifs <;> simp
    · rw [if_neg hut, map_zero]
      split_ifs with h1 h2 <;> simp_all)
  rw [hb, sub_eq_zero] at this; exact this

lemma g67e_F_comm (J : JMFamily D M) (t u : CellTableau Shape T) :
    jmSpectralProjector J t * jmSpectralProjector J u =
      jmSpectralProjector J u * jmSpectralProjector J t := by
  have := congrArg Subtype.val (g67e_comm J (g67e_Fb J t) (g67e_Fb J u))
  simpa only [Subalgebra.coe_mul, g67e_Fb_coe] using this

lemma g67e_LF_comm (J : JMFamily D M) (t : CellTableau Shape T) (i : Fin M) :
    J.L i * jmSpectralProjector J t = jmSpectralProjector J t * J.L i := by
  have := congrArg Subtype.val (g67e_comm J (jmGenerator J i) (g67e_Fb J t))
  simp only [Subalgebra.coe_mul, g67e_Fb_coe] at this
  exact this


lemma g67e_star_one : D.star 1 = 1 := by
  have h : ∀ x, D.star 1 * x = x := by
    intro x
    have := D.star_mul (D.star x) 1
    rw [mul_one, D.star_involutive x] at this
    exact this.symm
  simpa using h 1

lemma g67e_star_B (J : JMFamily D M) (b : A) (hb : b ∈ jmAlgebra J) : D.star b = b := by
  unfold jmAlgebra at hb
  induction hb using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact J.fixed i
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, g67e_star_one]
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | mul x y hx' hy' hx hy =>
    rw [D.star_mul, hx, hy]
    exact congrArg Subtype.val (g67e_comm J ⟨y, hy'⟩ ⟨x, hx'⟩)

def g67e_mu (z : CellIndex Shape T) : ℕ :=
  g67e_hsh z.1 * (2 * g67e_N T + 2) + g67e_pos z.2.1 + g67e_pos z.2.2

lemma g67e_mu_lt {z w : CellIndex Shape T} (h : g67e_prec z w) : g67e_mu z < g67e_mu w := by
  rcases h with h | ⟨v, hv, rfl⟩
  · have h1 := g67e_hsh_lt h
    have h2 := g67e_pos_le z.2.1
    have h3 := g67e_pos_le z.2.2
    unfold g67e_mu
    have : (g67e_hsh z.1 + 1) * (2 * g67e_N T + 2) ≤ g67e_hsh w.1 * (2 * g67e_N T + 2) :=
      Nat.mul_le_mul_right _ h1
    nlinarith
  · unfold g67e_mu
    have := g67e_pos_lt hv
    simp only
    omega

theorem g67e_gamma (J : JMFamily D M) (hsep : separatesAll J) (t : CellTableau Shape T) :
    seminormalGamma J t ≠ 0 := by
  set F := jmSpectralProjector J t with hFdef
  set zt : CellIndex Shape T := ⟨t.1, (t.2, t.2)⟩ with hzt
  set f := F * D.basis zt * F with hfdef
  have hFF : F * F = F := by rw [hFdef, g67e_FF J hsep, if_pos rfl]
  have hFB : F ∈ jmAlgebra J := by rw [hFdef, ← g67e_Fb_coe]; exact (g67e_Fb J t).2
  have hFg : g67e_good D F := g67e_jm_le J hFB
  have hphi : ∀ z, g67e_phi D z F = if (⟨z.1, z.2.2⟩ : CellTableau Shape T) = t then 1 else 0 := by
    intro z
    rw [hFdef, ← g67e_Fb_coe, ← g67e_chiZ_apply, g67e_chi_Fb J hsep]
  have hright : ∀ z, D.basis z * F - g67e_phi D z F • D.basis z ∈ g67e_Gt D z := by
    intro z
    obtain ⟨c, hc⟩ := hFg z
    rw [g67e_coef F z c hc]; exact hc
  have hstarF : D.star F = F := g67e_star_B J F hFB
  have hleft : ∀ z : CellIndex Shape T, ∃ y ∈ g67e_Gt D ⟨z.1, (z.2.2, z.2.1)⟩,
      F * D.basis z = g67e_phi D ⟨z.1, (z.2.2, z.2.1)⟩ F • D.basis z + D.star y := by
    intro z
    refine ⟨_, hright ⟨z.1, (z.2.2, z.2.1)⟩, ?_⟩
    rw [map_sub, D.star_mul, hstarF, map_smul, D.star_basis]
    abel
  -- the corner F A F is spanned by f
  set Sp := K ∙ f with hSp
  have hmuB : ∃ Bd, ∀ z : CellIndex Shape T, g67e_mu z < Bd :=
    ⟨Finset.univ.sup (g67e_mu (T := T)) + 1, fun z => by
      have := Finset.le_sup (f := g67e_mu (T := T)) (Finset.mem_univ z); omega⟩
  obtain ⟨Bd, hBd⟩ := hmuB
  have hcorner : ∀ k, ∀ z : CellIndex Shape T, Bd - g67e_mu z = k → F * D.basis z * F ∈ Sp := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro z hk
      have hGt : ∀ x ∈ g67e_Gt D z, F * x * F ∈ Sp := by
        intro x hx
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
        · rintro _ ⟨w, hw, rfl⟩
          have := g67e_mu_lt hw
          have := hBd w
          exact ih (Bd - g67e_mu w) (by omega) w rfl
        · simp
        · intro x y _ _ hx hy; rw [mul_add, add_mul]; exact Submodule.add_mem _ hx hy
        · intro c x _ hx; rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
      have hGs : ∀ y ∈ g67e_Gt D ⟨z.1, (z.2.2, z.2.1)⟩, F * D.star y * F ∈ Sp := by
        intro y hy
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨w, hw, rfl⟩
          rcases w with ⟨m, a, b⟩
          rw [D.star_basis]
          have h1 := g67e_mu_lt hw
          have h2 := hBd ⟨m, (b, a)⟩
          have e1 : g67e_mu (⟨m, (b, a)⟩ : CellIndex Shape T) = g67e_mu (⟨m, (a, b)⟩ : CellIndex Shape T) := by
            unfold g67e_mu; simp only; omega
          have e2 : g67e_mu (⟨z.1, (z.2.2, z.2.1)⟩ : CellIndex Shape T) = g67e_mu z := by
            unfold g67e_mu; simp only; omega
          exact ih (Bd - g67e_mu ⟨m, (b, a)⟩) (by omega) _ rfl
        · simp
        · intro x y _ _ hx hy; rw [map_add, mul_add, add_mul]; exact Submodule.add_mem _ hx hy
        · intro c x _ hx; rw [map_smul, mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
      by_cases hc : (⟨z.1, z.2.2⟩ : CellTableau Shape T) = t
      · by_cases hr : (⟨z.1, z.2.1⟩ : CellTableau Shape T) = t
        · have : z = zt := by
            rcases z with ⟨m, a, b⟩
            rw [hzt]
            subst hc
            simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hr
            rw [hr]
          rw [this]; exact Submodule.mem_span_singleton_self f
        · obtain ⟨y, hy, hyeq⟩ := hleft z
          rw [hphi, if_neg hr, zero_smul, zero_add] at hyeq
          have : F * D.basis z * F = F * D.star y * F := by
            rw [← hyeq, ← mul_assoc, hFF]
          rw [this]; exact hGs y hy
      · have hz := hright z
        rw [hphi, if_neg hc, zero_smul, sub_zero] at hz
        have : F * D.basis z * F = F * (D.basis z * F) * F := by
          rw [mul_assoc, mul_assoc, mul_assoc, hFF]
        rw [this]; exact hGt _ hz
  have hall : ∀ x : A, F * x * F ∈ Sp := by
    intro x
    rw [← D.basis.sum_repr x, Finset.mul_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ (fun z _ => ?_)
    rw [mul_smul_comm, smul_mul_assoc]
    exact Submodule.smul_mem _ _ (hcorner _ z rfl)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (show F ∈ Sp by
    have := hall 1; rwa [mul_one, hFF] at this)
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp (show f * f ∈ Sp by
    have : f * f = F * (D.basis zt * F * D.basis zt) * F := by
      simp only [hfdef, mul_assoc]; rw [← mul_assoc F F, hFF]
    rw [this]; exact hall _)
  have hF0 : F ≠ 0 := by
    intro h0
    have := hphi zt
    rw [if_pos rfl, h0] at this
    simp [g67e_phi] at this
  -- coefficient of a_zt in f is 1
  have hf1 : D.basis.repr f zt = 1 := by
    obtain ⟨y, hy, hyeq⟩ := hleft zt
    rw [hphi, if_pos rfl, one_smul] at hyeq
    have h1 := hright zt
    rw [hphi, if_pos rfl, one_smul] at h1
    have hfe : f = (D.basis zt * F - D.basis zt) + D.basis zt + D.star y * F := by
      rw [hfdef, hyeq, add_mul]; abel
    rw [hfe, map_add, map_add, Finsupp.add_apply, Finsupp.add_apply,
      g67e_repr_zero zt _ h1, Module.Basis.repr_self, Finsupp.single_eq_same]
    have : D.basis.repr (D.star y * F) zt = 0 := by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨w, hw, rfl⟩
        rcases w with ⟨m, a, b⟩
        rw [D.star_basis]
        have h1 := g67e_mu_lt hw
        have e1 : g67e_mu (⟨m, (b, a)⟩ : CellIndex Shape T) = g67e_mu (⟨m, (a, b)⟩ : CellIndex Shape T) := by
          unfold g67e_mu; simp only; omega
        have e3 : g67e_mu (⟨zt.1, (zt.2.2, zt.2.1)⟩ : CellIndex Shape T) = g67e_mu zt := rfl
        have e4 : g67e_mu zt = g67e_mu (⟨t.1, (t.2, t.2)⟩ : CellIndex Shape T) := rfl
        apply g67e_repr_good F hFg
        · intro e; have := congrArg g67e_mu e; omega
        · intro hp; have := g67e_mu_lt hp; omega
      · simp
      · intro x y _ _ hx hy; rw [map_add, add_mul, map_add, Finsupp.add_apply, hx, hy, add_zero]
      · intro c x _ hx
        rw [map_smul, smul_mul_assoc, map_smul, Finsupp.smul_apply, hx, smul_zero]
    rw [this]; ring
  have hf0 : f ≠ 0 := by
    intro h0; rw [h0, map_zero, Finsupp.zero_apply] at hf1; exact zero_ne_one hf1
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hr; exact hF0 hr.symm
  have key : r • f = (r * r * g) • f := by
    calc r • f = F := hr
      _ = F * F := hFF.symm
      _ = (r • f) * (r • f) := by rw [hr]
      _ = (r * r) • (f * f) := by rw [smul_mul_smul_comm]
      _ = (r * r * g) • f := by rw [← hg, smul_smul]
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_smul] at key
    exact hr0 ((smul_eq_zero.mp key).resolve_right hf0)
  have hgam : seminormalGamma J t = g := by
    unfold seminormalGamma seminormal
    show D.basis.repr (f * f) zt = g
    rw [← hg, map_smul, Finsupp.smul_apply, hf1, smul_eq_mul, mul_one]
  rw [hgam]; exact hg0

end G67EJ

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

theorem g68n_stb (J : JMFamily D M)
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

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section G68N1
variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

lemma g68n_chi_eval (J : JMFamily D M) (z : CellIndex Shape T) (i : Fin M) (q : Polynomial K) :
    g67e_chiZ J z (Polynomial.aeval (jmGenerator J i) q) = q.eval (J.content ⟨z.1, z.2.2⟩ i) := by
  rw [← Polynomial.aeval_algHom_apply, g67e_chi_gen]
  simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

lemma g68n_aeval_val (J : JMFamily D M) (i : Fin M) (q : Polynomial K) :
    ((Polynomial.aeval (jmGenerator J i) q : jmAlgebra J) : A) = Polynomial.aeval (J.L i) q := by
  have := Polynomial.aeval_algHom_apply (jmAlgebra J).val (jmGenerator J i) q
  exact this.symm

lemma g68n_Lsum (J : JMFamily D M) (hsep : separatesAll J) (i : Fin M) :
    J.L i = ∑ t : CellTableau Shape T, J.content t i • jmSpectralProjector J t := by
  let b : jmAlgebra J := jmGenerator J i - ∑ t, J.content t i • g67e_Fb J t
  have hb : (b : A) = J.L i - ∑ t : CellTableau Shape T, J.content t i • jmSpectralProjector J t := by
    simp only [b, Subalgebra.coe_sub, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, g67e_Fb_coe]; rfl
  have := g67e_ss J hsep (b : A) b.2 (fun z => by
    rw [← g67e_chiZ_apply]
    simp only [b, map_sub, map_sum, map_smul, g67e_chi_Fb J hsep, g67e_chi_gen, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring)
  rw [hb, sub_eq_zero] at this; exact this

lemma g68n_Fsum (J : JMFamily D M) (hsep : separatesAll J) :
    ∑ t : CellTableau Shape T, jmSpectralProjector J t = 1 := by
  let b : jmAlgebra J := ∑ t, g67e_Fb J t - 1
  have hb : (b : A) = ∑ t : CellTableau Shape T, jmSpectralProjector J t - 1 := by
    simp only [b, Subalgebra.coe_sub, AddSubmonoidClass.coe_finset_sum, g67e_Fb_coe, Subalgebra.coe_one]
  have := g67e_ss J hsep (b : A) b.2 (fun z => by
    rw [← g67e_chiZ_apply]
    simp only [b, map_sub, map_sum, g67e_chi_Fb J hsep, map_one, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_self])
  rw [hb, sub_eq_zero] at this; exact this

lemma g68n_minpoly (J : JMFamily D M) (hsep : separatesAll J) (i : Fin M) :
    minpoly K (J.L i) = ∏ c ∈ contents J i, (Polynomial.X - Polynomial.C c) := by
  set p : Polynomial K := ∏ c ∈ contents J i, (Polynomial.X - Polynomial.C c) with hp
  have hroot : ∀ q : Polynomial K, Polynomial.aeval (J.L i) q = 0 →
      ∀ c ∈ contents J i, q.eval c = 0 := by
    intro q hq c hc
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hc
    have h0 : (Polynomial.aeval (jmGenerator J i) q : jmAlgebra J) = 0 := by
      apply Subtype.ext; rw [g68n_aeval_val]; exact hq
    have := g68n_chi_eval J ⟨t.1, (t.2, t.2)⟩ i q
    rw [h0, map_zero] at this
    exact this.symm
  have hpmon : p.Monic := Polynomial.monic_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C c)
  have hpz : Polynomial.aeval (J.L i) p = 0 := by
    rw [← g68n_aeval_val]
    have : (Polynomial.aeval (jmGenerator J i) p : jmAlgebra J) = 0 := by
      apply Subtype.ext
      apply g67e_ss J hsep _ (Polynomial.aeval (jmGenerator J i) p).2
      intro z
      rw [← g67e_chiZ_apply, g68n_chi_eval, hp, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_image.mpr ⟨(⟨z.1, z.2.2⟩ : CellTableau Shape T), Finset.mem_univ _, rfl⟩) (by simp)
    rw [this]; rfl
  have hdvd : ∀ q : Polynomial K, q ≠ 0 → Polynomial.aeval (J.L i) q = 0 → p ∣ q := by
    intro q hq0 hq
    have hle : (contents J i).val ≤ q.roots := by
      rw [Multiset.le_iff_subset (contents J i).nodup]
      intro c hc
      rw [Polynomial.mem_roots hq0]
      exact hroot q hq c hc
    have h1 := Polynomial.prod_multiset_X_sub_C_dvd q
    refine dvd_trans ?_ h1
    rw [hp, Finset.prod_eq_multiset_prod]
    exact Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)
  symm
  refine minpoly.unique K (J.L i) hpmon hpz (fun q hqm hq => ?_)
  exact Polynomial.degree_le_of_dvd (hdvd q hqm.ne_zero hq) hqm.ne_zero

theorem g68n_spec (J : JMFamily D M) (hsep : separatesAll J) (i : Fin M) :
    J.L i = ∑ t : CellTableau Shape T, J.content t i • jmSpectralProjector J t ∧
    minpoly K (J.L i) = ∏ c ∈ contents J i, (Polynomial.X - Polynomial.C c) :=
  ⟨g68n_Lsum J hsep i, g68n_minpoly J hsep i⟩

end G68N1

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section G68N2
variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

lemma g68n_sepC (J : JMFamily D M) (hsep : separatesAll J) : separatesComparable J := by
  intro s t _ hst
  by_contra h
  push_neg at h
  exact hst (hsep (funext h))

def g68n_fb (J : JMFamily D M) (hsep : separatesAll J) : Module.Basis (CellIndex Shape T) K A :=
  Classical.choose (g68n_stb J (g68n_sepC J hsep)).2.1

lemma g68n_fb_apply (J : JMFamily D M) (hsep : separatesAll J) (z : CellIndex Shape T) :
    g68n_fb J hsep z = seminormal J z :=
  Classical.choose_spec (g68n_stb J (g68n_sepC J hsep)).2.1 z

lemma g68n_star_f (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (s t : T l) :
    D.star (seminormal J ⟨l, (s, t)⟩) = seminormal J ⟨l, (t, s)⟩ :=
  (g68n_stb J (g68n_sepC J hsep)).2.2 l s t

lemma g68n_fF (J : JMFamily D M) (hsep : separatesAll J) (z : CellIndex Shape T) (u : CellTableau Shape T) :
    seminormal J z * jmSpectralProjector J u =
      if u = ⟨z.1, z.2.2⟩ then seminormal J z else 0 := by
  unfold seminormal
  rw [mul_assoc, g67e_FF J hsep]
  split_ifs <;> simp

lemma g68n_Ff (J : JMFamily D M) (hsep : separatesAll J) (z : CellIndex Shape T) (u : CellTableau Shape T) :
    jmSpectralProjector J u * seminormal J z =
      if u = ⟨z.1, z.2.1⟩ then seminormal J z else 0 := by
  unfold seminormal
  rw [← mul_assoc, ← mul_assoc, g67e_F_comm, g67e_FF J hsep]
  split_ifs <;> simp [mul_assoc]

lemma g68n_FfF (J : JMFamily D M) (hsep : separatesAll J) (u v : CellTableau Shape T)
    (z : CellIndex Shape T) :
    jmSpectralProjector J u * seminormal J z * jmSpectralProjector J v =
      if (⟨z.1, z.2.1⟩ : CellTableau Shape T) = u ∧ (⟨z.1, z.2.2⟩ : CellTableau Shape T) = v
      then seminormal J z else 0 := by
  rw [g68n_Ff J hsep]
  by_cases h1 : u = ⟨z.1, z.2.1⟩
  · rw [if_pos h1, g68n_fF J hsep]
    by_cases h2 : v = ⟨z.1, z.2.2⟩
    · rw [if_pos h2, if_pos ⟨h1.symm, h2.symm⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.2.symm)]
  · rw [if_neg h1, zero_mul, if_neg (fun h => h1 h.1.symm)]

lemma g68n_FxF (J : JMFamily D M) (hsep : separatesAll J) (u v : CellTableau Shape T) (x : A) :
    jmSpectralProjector J u * x * jmSpectralProjector J v =
      ∑ z ∈ Finset.univ.filter (fun z : CellIndex Shape T =>
        (⟨z.1, z.2.1⟩ : CellTableau Shape T) = u ∧ (⟨z.1, z.2.2⟩ : CellTableau Shape T) = v),
        (g68n_fb J hsep).repr x z • seminormal J z := by
  conv_lhs => rw [← (g68n_fb J hsep).sum_repr x]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, g68n_fb_apply, g68n_FfF J hsep]
  split_ifs <;> simp

def g68n_zt (t : CellTableau Shape T) : CellIndex Shape T := ⟨t.1, (t.2, t.2)⟩

lemma g68n_filter_tt (t : CellTableau Shape T) :
    Finset.univ.filter (fun z : CellIndex Shape T =>
        (⟨z.1, z.2.1⟩ : CellTableau Shape T) = t ∧ (⟨z.1, z.2.2⟩ : CellTableau Shape T) = t) =
      {g68n_zt t} := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩; exact g67d_idx_ext h1 h2
  · rintro rfl; exact ⟨rfl, rfl⟩

lemma g68n_FxF_tt (J : JMFamily D M) (hsep : separatesAll J) (t : CellTableau Shape T) (x : A) :
    jmSpectralProjector J t * x * jmSpectralProjector J t =
      (g68n_fb J hsep).repr x (g68n_zt t) • seminormal J (g68n_zt t) := by
  rw [g68n_FxF J hsep, g68n_filter_tt, Finset.sum_singleton]

lemma g68n_F_ne (J : JMFamily D M) (hsep : separatesAll J) (t : CellTableau Shape T) :
    jmSpectralProjector J t ≠ 0 := by
  intro h
  have h1 : g67e_chiZ J (g68n_zt t) (g67e_Fb J t) = 1 := by
    rw [g67e_chi_Fb J hsep]; simp [g68n_zt]
  have h0 : g67e_Fb J t = 0 := Subtype.ext (by rw [g67e_Fb_coe, h]; rfl)
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

lemma g68n_F_f (J : JMFamily D M) (hsep : separatesAll J) (t : CellTableau Shape T) :
    ∃ c : K, c ≠ 0 ∧ jmSpectralProjector J t = c • seminormal J (g68n_zt t) := by
  have h := g68n_FxF_tt J hsep t 1
  rw [mul_one, g67e_FF J hsep, if_pos rfl] at h
  refine ⟨_, fun hc => g68n_F_ne J hsep t (by rw [h, hc, zero_smul]), h⟩

lemma g68n_ftt_mem (J : JMFamily D M) (hsep : separatesAll J) (t : CellTableau Shape T) :
    seminormal J (g68n_zt t) ∈ jmAlgebra J := by
  obtain ⟨c, hc, h⟩ := g68n_F_f J hsep t
  have : seminormal J (g68n_zt t) = c⁻¹ • jmSpectralProjector J t := by
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [this]
  exact Subalgebra.smul_mem _ (g67d_proj_mem J t) _

theorem g68n_maxab (J : JMFamily D M) (hsep : separatesAll J) :
    MaximalAbelian (jmAlgebra J) := by
  refine ⟨fun x hx y hy => g67d_jm_comm J hx hy, fun C hBC hC => ?_⟩
  refine le_antisymm (fun x hx => ?_) hBC
  have hcomm : ∀ u, jmSpectralProjector J u * x = x * jmSpectralProjector J u :=
    fun u => hC _ (hBC (g67d_proj_mem J u)) x hx
  have hx' : x = ∑ u, jmSpectralProjector J u * x * jmSpectralProjector J u := by
    conv_lhs => rw [← mul_one x, ← g68n_Fsum J hsep, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [hcomm, mul_assoc, g67e_FF J hsep, if_pos rfl]
  rw [hx']
  refine Subalgebra.sum_mem _ (fun u _ => ?_)
  rw [g68n_FxF_tt J hsep]
  exact Subalgebra.smul_mem _ (g68n_ftt_mem J hsep u) _

end G68N2

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section G68N3
variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

variable (D) in
def g68n_I (l : Shape) : Submodule K A :=
  Submodule.span K {x | ∃ w : CellIndex Shape T, l ≤ w.1 ∧ x = D.basis w}

lemma g68n_higher_I {l m : Shape} (h : l ≤ m) : higherSpan (R := K) D.basis m ≤ g68n_I D l := by
  apply Submodule.span_le.mpr
  rintro _ ⟨m', s, t, hm, rfl⟩
  exact Submodule.subset_span ⟨⟨m', (s, t)⟩, le_trans h hm.le, rfl⟩

lemma g68n_higher_repr {m l : Shape} (hml : ¬ m < l) (p : T l × T l) (x : A)
    (hx : x ∈ higherSpan (R := K) D.basis m) : D.basis.repr x ⟨l, p⟩ = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m', s, t, hm, rfl⟩ := hx
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg]
    intro h
    have : m' = l := congrArg Sigma.fst h
    subst this
    exact hml hm
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

lemma g68n_I_mul (l : Shape) (x : A) (hx : x ∈ g68n_I D l) (y : A) : x * y ∈ g68n_I D l := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨m, s, t⟩, hlm, rfl⟩ := hx
    obtain ⟨r, hr⟩ := D.multiplication m t y
    have e : D.basis ⟨m, (s, t)⟩ * y = (D.basis ⟨m, (s, t)⟩ * y -
        ∑ v : T m, r v • D.basis ⟨m, (s, v)⟩) + ∑ v : T m, r v • D.basis ⟨m, (s, v)⟩ := by abel
    rw [e]
    refine Submodule.add_mem _ (g68n_higher_I hlm (hr s)) (Submodule.sum_mem _ (fun v _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨m, (s, v)⟩, hlm, rfl⟩)))
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

lemma g68n_I_star (l : Shape) (x : A) (hx : x ∈ g68n_I D l) : D.star x ∈ g68n_I D l := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨m, s, t⟩, hlm, rfl⟩ := hx
    rw [D.star_basis]
    exact Submodule.subset_span ⟨⟨m, (t, s)⟩, hlm, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

lemma g68n_I_lmul (l : Shape) (x : A) (hx : x ∈ g68n_I D l) (y : A) : y * x ∈ g68n_I D l := by
  have := g68n_I_star l _ (g68n_I_mul l (D.star x) (g68n_I_star l x hx) (D.star y))
  rwa [D.star_mul, D.star_involutive, D.star_involutive] at this

lemma g68n_basis_I (l : Shape) (s t : T l) : D.basis ⟨l, (s, t)⟩ ∈ g68n_I D l :=
  Submodule.subset_span ⟨⟨l, (s, t)⟩, le_rfl, rfl⟩

variable (D) in
def g68n_rho (l : Shape) (w : T l) (y : A) : T l → K := Classical.choose (D.multiplication l w y)

lemma g68n_rho_spec (l : Shape) (w : T l) (y : A) (s : T l) :
    D.basis ⟨l, (s, w)⟩ * y - ∑ v, g68n_rho D l w y v • D.basis ⟨l, (s, v)⟩ ∈
      higherSpan (R := K) D.basis l :=
  Classical.choose_spec (D.multiplication l w y) s

lemma g68n_K (l : Shape) (x : A) (hx : x ∈ g68n_I D l) (y : A) (s v : T l) :
    D.basis.repr (x * y) ⟨l, (s, v)⟩ =
      ∑ w, D.basis.repr x ⟨l, (s, w)⟩ * g68n_rho D l w y v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨m, s', t'⟩, hlm, rfl⟩ := hx
    rcases eq_or_lt_of_le hlm with h | h
    · subst h
      have e := g68n_rho_spec (D := D) l t' y s'
      have e2 : D.basis ⟨l, (s', t')⟩ * y = (D.basis ⟨l, (s', t')⟩ * y -
          ∑ v, g68n_rho D l t' y v • D.basis ⟨l, (s', v)⟩) +
          ∑ v, g68n_rho D l t' y v • D.basis ⟨l, (s', v)⟩ := by abel
      rw [e2, map_add, Finsupp.add_apply, g68n_higher_repr (lt_irrefl l) _ _ e, zero_add]
      simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum,
        Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
        Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero,
        ite_mul, one_mul, zero_mul]
      by_cases hs : s' = s
      · subst hs; simp
      · simp [hs]
    · have hne : ∀ w : T l, D.basis.repr (D.basis ⟨m, (s', t')⟩) ⟨l, (s, w)⟩ = 0 := by
        intro w
        rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg]
        intro e; exact (ne_of_lt h) (congrArg Sigma.fst e).symm
      simp only [hne, zero_mul, Finset.sum_const_zero]
      have hm := g68n_I_mul (D := D) m _ (Submodule.subset_span ⟨⟨m, (s', t')⟩, le_rfl, rfl⟩) y
      -- elements of I m have zero coefficient on shape l < m
      have key : ∀ z ∈ g68n_I D m, D.basis.repr z ⟨l, (s, v)⟩ = 0 := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨w, hw, rfl⟩ := hz
          rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg]
          intro e
          have : w.1 = l := congrArg Sigma.fst e
          rw [this] at hw
          exact absurd (lt_of_lt_of_le h hw) (lt_irrefl _)
        | zero => simp
        | add x y _ _ hx hy => simp [hx, hy]
        | smul c x _ hx => simp [hx]
      exact key _ hm
  | zero => simp
  | add x x' _ _ hx hx' =>
    rw [add_mul, map_add, Finsupp.add_apply, hx, hx', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [map_add, Finsupp.add_apply, add_mul]
  | smul c x _ hx =>
    rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, hx, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc]

lemma g68n_repr_star (x : A) (l : Shape) (s t : T l) :
    D.basis.repr (D.star x) ⟨l, (s, t)⟩ = D.basis.repr x ⟨l, (t, s)⟩ := by
  conv_lhs => rw [← D.basis.sum_repr x]
  rw [map_sum, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single (⟨l, (t, s)⟩ : CellIndex Shape T)]
  · rw [map_smul, D.star_basis, map_smul, Module.Basis.repr_self]; simp
  · rintro ⟨m, a, b⟩ _ hne
    rw [map_smul, D.star_basis, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, if_neg, smul_zero]
    intro e
    obtain ⟨rfl, e'⟩ := Sigma.mk.inj_iff.mp e
    have := eq_of_heq e'
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact hne rfl
  · simp

lemma g68n_f_one (J : JMFamily D M) (z : CellIndex Shape T) :
    D.basis.repr (seminormal J z) z = 1 := by
  have h := g67d_Up_repr z _ (g67d_semi_sub J z) z (g67d_pd_irrefl z)
  rw [map_sub, Finsupp.sub_apply, Module.Basis.repr_self, Finsupp.single_eq_same, sub_eq_zero] at h
  exact h

lemma g68n_aF (J : JMFamily D M) (l : Shape) (s t w : T l) :
    D.basis.repr (D.basis ⟨l, (t, s)⟩ * jmSpectralProjector J ⟨l, s⟩) ⟨l, (w, s)⟩ =
      if w = t then 1 else 0 := by
  split_ifs with hw
  · subst hw
    have h := g67d_Up_repr _ _ (g67d_lead_right J ⟨l, (w, s)⟩) _ (g67d_pd_irrefl _)
    rw [map_sub, Finsupp.sub_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      sub_eq_zero] at h
    exact h
  · rw [g68n_K l _ (g68n_basis_I l t s)]
    refine Finset.sum_eq_zero (fun w' _ => ?_)
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg, zero_mul]
    intro e
    obtain ⟨-, e'⟩ := Sigma.mk.inj_iff.mp e
    have := eq_of_heq e'
    simp only [Prod.mk.injEq] at this
    exact hw this.1.symm

lemma g68n_Fa (J : JMFamily D M) (l : Shape) (s t w : T l) :
    D.basis.repr (jmSpectralProjector J ⟨l, s⟩ * D.basis ⟨l, (s, t)⟩) ⟨l, (s, w)⟩ =
      if w = t then 1 else 0 := by
  rw [← g68n_aF J l s t w, ← g68n_repr_star, D.star_mul, D.star_basis,
    g67d_star_jm J _ (g67d_proj_mem J _)]

lemma g68n_f_I (J : JMFamily D M) (l : Shape) (s t : T l) :
    seminormal J ⟨l, (s, t)⟩ ∈ g68n_I D l := by
  unfold seminormal
  exact g68n_I_mul l _ (g68n_I_lmul l _ (g68n_basis_I l s t) _) _

lemma g68n_f_row (J : JMFamily D M) (l : Shape) (s t w : T l) :
    D.basis.repr (seminormal J ⟨l, (s, t)⟩) ⟨l, (s, w)⟩ =
      g68n_rho D l t (jmSpectralProjector J ⟨l, t⟩) w := by
  unfold seminormal
  rw [g68n_K l _ (g68n_I_lmul l _ (g68n_basis_I l s t) _)]
  simp only [g68n_Fa, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def g68n_d (J : JMFamily D M) (l : Shape) (s t v : T l) : K :=
  D.basis.repr (seminormal J ⟨l, (s, t)⟩ * seminormal J ⟨l, (t, v)⟩) ⟨l, (s, v)⟩

lemma g68n_d_indep (J : JMFamily D M) (l : Shape) (s s' t v : T l) :
    g68n_d J l s t v = g68n_d J l s' t v := by
  unfold g68n_d
  rw [g68n_K l _ (g68n_f_I J l s t), g68n_K l _ (g68n_f_I J l s' t)]
  simp only [g68n_f_row]

lemma g68n_prod_eq (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (s t v : T l) :
    seminormal J ⟨l, (s, t)⟩ * seminormal J ⟨l, (t, v)⟩ =
      g68n_d J l s t v • seminormal J ⟨l, (s, v)⟩ := by
  have h1 : seminormal J ⟨l, (s, t)⟩ * seminormal J ⟨l, (t, v)⟩ =
      jmSpectralProjector J ⟨l, s⟩ * (seminormal J ⟨l, (s, t)⟩ * seminormal J ⟨l, (t, v)⟩) *
        jmSpectralProjector J ⟨l, v⟩ := by
    rw [← mul_assoc, g68n_Ff J hsep, if_pos rfl, mul_assoc, g68n_fF J hsep, if_pos rfl]
  have hfil : Finset.univ.filter (fun z : CellIndex Shape T =>
      (⟨z.1, z.2.1⟩ : CellTableau Shape T) = ⟨l, s⟩ ∧ (⟨z.1, z.2.2⟩ : CellTableau Shape T) = ⟨l, v⟩) =
      {⟨l, (s, v)⟩} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact g67d_idx_ext (y := ⟨l, (s, v)⟩) h1 h2
    · rintro rfl; exact ⟨rfl, rfl⟩
  have h2 := h1
  rw [g68n_FxF J hsep, hfil, Finset.sum_singleton] at h2
  have hc : (g68n_fb J hsep).repr (seminormal J ⟨l, (s, t)⟩ * seminormal J ⟨l, (t, v)⟩)
      ⟨l, (s, v)⟩ = g68n_d J l s t v := by
    unfold g68n_d
    conv_rhs => rw [h2]
    simp only [map_smul, Finsupp.smul_apply, g68n_f_one, smul_eq_mul, mul_one]
  rw [← hc]; exact h2

lemma g68n_f_ne (J : JMFamily D M) (z : CellIndex Shape T) : seminormal J z ≠ 0 := by
  intro h
  have := g68n_f_one J z
  rw [h, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
  exact zero_ne_one this

lemma g68n_d_symm (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (s t v : T l) :
    g68n_d J l s t v = g68n_d J l v t s := by
  have h := congrArg D.star (g68n_prod_eq J hsep l s t v)
  rw [D.star_mul, map_smul, g68n_star_f J hsep, g68n_star_f J hsep, g68n_star_f J hsep,
    g68n_prod_eq J hsep l v t s] at h
  have := sub_eq_zero.mpr h
  rw [← sub_smul] at this
  exact (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right (g68n_f_ne J _))).symm

lemma g68n_d_gamma (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (s t v : T l) :
    g68n_d J l s t v = seminormalGamma J ⟨l, t⟩ := by
  rw [g68n_d_indep J l s t t v, g68n_d_symm J hsep, g68n_d_indep J l v t t t]
  rfl

theorem g68n_mult (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (s t u v : T l) :
    seminormal J ⟨l, (s, t)⟩ * seminormal J ⟨l, (u, v)⟩ =
      if t = u then seminormalGamma J ⟨l, t⟩ • seminormal J ⟨l, (s, v)⟩ else 0 := by
  split_ifs with h
  · subst h; rw [g68n_prod_eq J hsep, g68n_d_gamma J hsep]
  · unfold seminormal
    have : jmSpectralProjector J ⟨l, s⟩ * D.basis ⟨l, (s, t)⟩ * jmSpectralProjector J ⟨l, t⟩ *
        (jmSpectralProjector J ⟨l, u⟩ * D.basis ⟨l, (u, v)⟩ * jmSpectralProjector J ⟨l, v⟩) =
        jmSpectralProjector J ⟨l, s⟩ * D.basis ⟨l, (s, t)⟩ *
        (jmSpectralProjector J ⟨l, t⟩ * jmSpectralProjector J ⟨l, u⟩) *
        (D.basis ⟨l, (u, v)⟩ * jmSpectralProjector J ⟨l, v⟩) := by noncomm_ring
    rw [this, g67e_FF J hsep, if_neg (fun e => h (eq_of_heq (Sigma.mk.inj_iff.mp e).2).symm)]
    simp

theorem g68n_mult2 (J : JMFamily D M) (hsep : separatesAll J) (l m : Shape) (hlm : l ≠ m)
    (s t : T l) (u v : T m) :
    seminormal J ⟨l, (s, t)⟩ * seminormal J ⟨m, (u, v)⟩ = 0 := by
  unfold seminormal
  have : jmSpectralProjector J ⟨l, s⟩ * D.basis ⟨l, (s, t)⟩ * jmSpectralProjector J ⟨l, t⟩ *
      (jmSpectralProjector J ⟨m, u⟩ * D.basis ⟨m, (u, v)⟩ * jmSpectralProjector J ⟨m, v⟩) =
      jmSpectralProjector J ⟨l, s⟩ * D.basis ⟨l, (s, t)⟩ *
      (jmSpectralProjector J ⟨l, t⟩ * jmSpectralProjector J ⟨m, u⟩) *
      (D.basis ⟨m, (u, v)⟩ * jmSpectralProjector J ⟨m, v⟩) := by noncomm_ring
  rw [this, g67e_FF J hsep, if_neg (fun e => hlm (congrArg Sigma.fst e).symm)]
  simp

end G68N3

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section G68N4
variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

lemma g68n_fx (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (s t : T l) (x : A) :
    seminormal J ⟨l, (s, t)⟩ * x =
      ∑ v : T l, ((g68n_fb J hsep).repr x ⟨l, (t, v)⟩ * seminormalGamma J ⟨l, t⟩) •
        seminormal J ⟨l, (s, v)⟩ := by
  conv_lhs => rw [← (g68n_fb J hsep).sum_repr x]
  rw [Finset.mul_sum, Fintype.sum_sigma, Finset.sum_eq_single l]
  · rw [Fintype.sum_prod_type]
    simp_rw [mul_smul_comm, g68n_fb_apply, g68n_mult J hsep, smul_ite, smul_zero, smul_smul]
    rw [Finset.sum_eq_single t]
    · simp
    · intro u _ hu; simp [Ne.symm hu]
    · simp
  · intro m _ hm
    refine Finset.sum_eq_zero (fun p _ => ?_)
    obtain ⟨u, v⟩ := p
    rw [mul_smul_comm, g68n_fb_apply, g68n_mult2 J hsep l m (Ne.symm hm), smul_zero]
  · simp

theorem g68n_cellular (J : JMFamily D M) (hsep : separatesAll J) :
    IsCellularFamily D (seminormal J) := by
  refine ⟨CellDatum.mk (g68n_fb J hsep) D.star D.star_involutive D.star_mul ?_ ?_,
    fun z => g68n_fb_apply J hsep z, rfl⟩
  · intro l s t
    rw [g68n_fb_apply, g68n_fb_apply, g68n_star_f J hsep]
  · intro l t x
    refine ⟨fun v => (g68n_fb J hsep).repr x ⟨l, (t, v)⟩ * seminormalGamma J ⟨l, t⟩, fun s => ?_⟩
    simp only [g68n_fb_apply]
    rw [g68n_fx J hsep, sub_self]
    exact Submodule.zero_mem _

theorem g68n_semimult (J : JMFamily D M) (hsep : separatesAll J) :
    (∀ l (s t u v : T l),
      seminormal J ⟨l, (s, t)⟩ * seminormal J ⟨l, (u, v)⟩ =
        if t = u then seminormalGamma J ⟨l, t⟩ • seminormal J ⟨l, (s, v)⟩ else 0) ∧
    (∀ l m, l ≠ m → ∀ (s t : T l) (u v : T m),
      seminormal J ⟨l, (s, t)⟩ * seminormal J ⟨m, (u, v)⟩ = 0) ∧
    IsCellularFamily D (seminormal J) :=
  ⟨g68n_mult J hsep, g68n_mult2 J hsep, g68n_cellular J hsep⟩

lemma g68n_F_gam (J : JMFamily D M) (hsep : separatesAll J) (t : CellTableau Shape T) :
    jmSpectralProjector J t = (seminormalGamma J t)⁻¹ • seminormal J ⟨t.1, (t.2, t.2)⟩ := by
  obtain ⟨c, hc, h⟩ := g68n_F_f J hsep t
  have hFF := g67e_FF J hsep t t
  rw [if_pos rfl] at hFF
  rw [h, smul_mul_smul_comm] at hFF
  unfold g68n_zt at hFF
  rw [g68n_mult J hsep, if_pos rfl, smul_smul] at hFF
  have h2 := sub_eq_zero.mpr hFF
  rw [← sub_smul] at h2
  have h3 := (smul_eq_zero.mp h2).resolve_right (g68n_f_ne J _)
  have hg : c * seminormalGamma J t = 1 := by
    have : c * c * seminormalGamma J ⟨t.1, t.2⟩ = c := sub_eq_zero.mp h3
    have h4 : c * (c * seminormalGamma J t - 1) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc]; exact sub_eq_zero.mpr this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left hc)
  rw [h, inv_eq_of_mul_eq_one_left hg]
  rfl

lemma g68n_FxF_F (J : JMFamily D M) (hsep : separatesAll J) (t : CellTableau Shape T) (x : A) :
    ∃ b : K, jmSpectralProjector J t * x * jmSpectralProjector J t = b • jmSpectralProjector J t := by
  rw [g68n_FxF_tt J hsep]
  obtain ⟨c, hc, h⟩ := g68n_F_f J hsep t
  refine ⟨(g68n_fb J hsep).repr x (g68n_zt t) * c⁻¹, ?_⟩
  rw [h, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]

lemma g68n_idem_K {b : K} (h : b * b = b) : b = 0 ∨ b = 1 := by
  have : b * (b - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

lemma g68n_prim (J : JMFamily D M) (hsep : separatesAll J) (t : CellTableau Shape T) :
    PrimitiveIdempotent (jmSpectralProjector J t) := by
  set F := jmSpectralProjector J t
  have hFF : F * F = F := by rw [g67e_FF J hsep, if_pos rfl]
  refine ⟨hFF, g68n_F_ne J hsep t, fun f g hf hg hfg hgf he => ?_⟩
  have hFf : F * f = f := by rw [he, add_mul, hf, hgf, add_zero]
  have hfF : f * F = f := by rw [he, mul_add, hf, hfg, add_zero]
  have h1 : F * f * F = f := by rw [hFf, hfF]
  obtain ⟨b, hb⟩ := g68n_FxF_F J hsep t f
  rw [h1] at hb
  have hb2 : (b * b) • F = b • F := by
    have := hf
    rw [hb, smul_mul_smul_comm, hFF] at this
    exact this
  have hFne := g68n_F_ne J hsep t
  have : b * b = b := by
    have := sub_eq_zero.mpr hb2
    rw [← sub_smul] at this
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hFne)
  rcases g68n_idem_K this with h0 | h0
  · left; rw [hb, h0, zero_smul]
  · right
    have : g = F - f := by rw [he]; abel
    rw [this, hb, h0, one_smul, sub_self]

lemma g68n_sum_ind (l : Shape) (X : CellTableau Shape T) (y : A) :
    ∑ t : T l, (if (⟨l, t⟩ : CellTableau Shape T) = X then y else 0) =
      if X.1 = l then y else 0 := by
  obtain ⟨m, u⟩ := X
  by_cases hm : m = l
  · subst hm
    rw [if_pos rfl, Finset.sum_eq_single u]
    · simp
    · intro t _ ht; rw [if_neg]; intro e; exact ht (eq_of_heq (Sigma.mk.inj_iff.mp e).2)
    · simp
  · rw [if_neg hm]
    exact Finset.sum_eq_zero (fun t _ => by
      rw [if_neg]; intro e; exact hm (congrArg Sigma.fst e).symm)

lemma g68n_EF (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (u : CellTableau Shape T) :
    shapeProjector J l * jmSpectralProjector J u =
      if u.1 = l then jmSpectralProjector J u else 0 := by
  unfold shapeProjector
  rw [Finset.sum_mul]
  simp_rw [g67e_FF J hsep]
  rw [← g68n_sum_ind l u]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases h : u = ⟨l, t⟩
  · rw [if_pos h, if_pos h.symm, h]
  · rw [if_neg h, if_neg (Ne.symm h)]

lemma g68n_FE (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (u : CellTableau Shape T) :
    jmSpectralProjector J u * shapeProjector J l =
      if u.1 = l then jmSpectralProjector J u else 0 := by
  unfold shapeProjector
  rw [Finset.mul_sum]
  simp_rw [g67e_F_comm J u, g67e_FF J hsep]
  rw [← g68n_sum_ind l u]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases h : u = ⟨l, t⟩
  · rw [if_pos h, if_pos h.symm, h]
  · rw [if_neg h, if_neg (Ne.symm h)]

lemma g68n_Ef (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (z : CellIndex Shape T) :
    shapeProjector J l * seminormal J z = if z.1 = l then seminormal J z else 0 := by
  unfold shapeProjector
  rw [Finset.sum_mul]
  simp_rw [g68n_Ff J hsep]
  exact g68n_sum_ind l ⟨z.1, z.2.1⟩ _

lemma g68n_fE (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (z : CellIndex Shape T) :
    seminormal J z * shapeProjector J l = if z.1 = l then seminormal J z else 0 := by
  unfold shapeProjector
  rw [Finset.mul_sum]
  simp_rw [g68n_fF J hsep]
  exact g68n_sum_ind l ⟨z.1, z.2.2⟩ _

lemma g68n_E_central (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) :
    Central (shapeProjector J l) := by
  intro a
  conv_lhs => rw [← (g68n_fb J hsep).sum_repr a]
  conv_rhs => rw [← (g68n_fb J hsep).sum_repr a]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, g68n_fb_apply, g68n_Ef J hsep, g68n_fE J hsep]

lemma g68n_EE (J : JMFamily D M) (hsep : separatesAll J) (l m : Shape) :
    shapeProjector J l * shapeProjector J m = if m = l then shapeProjector J m else 0 := by
  have : shapeProjector J m = ∑ u : T m, jmSpectralProjector J ⟨m, u⟩ := rfl
  rw [this, Finset.mul_sum]
  simp_rw [g68n_EF J hsep]
  split_ifs with h
  · rfl
  · simp

lemma g68n_Esum (J : JMFamily D M) (hsep : separatesAll J) :
    ∑ l, shapeProjector J l = 1 := by
  unfold shapeProjector
  rw [← g68n_Fsum J hsep, Fintype.sum_sigma]

theorem g68n_primproj (J : JMFamily D M) (hsep : separatesAll J)
    (hne : ∀ l, Nonempty (T l)) :
    (∀ t : CellTableau Shape T,
      jmSpectralProjector J t = (seminormalGamma J t)⁻¹ • seminormal J ⟨t.1, (t.2, t.2)⟩ ∧
      PrimitiveIdempotent (jmSpectralProjector J t)) ∧
    (∀ l, PrimitiveCentralIdempotent (shapeProjector J l)) ∧
    QAlgorithms.Papers.Independent.Support21.P08.CompleteOrthogonalIdempotents (jmSpectralProjector J) ∧
    QAlgorithms.Papers.Independent.Support21.P08.CompleteOrthogonalIdempotents (shapeProjector J) := by
  refine ⟨fun t => ⟨g68n_F_gam J hsep t, g68n_prim J hsep t⟩, fun l => ?_,
    ⟨fun i => by rw [g67e_FF J hsep, if_pos rfl], fun i j hij => by rw [g67e_FF J hsep, if_neg (Ne.symm hij)],
      g68n_Fsum J hsep⟩,
    ⟨fun i => by rw [g68n_EE J hsep, if_pos rfl], fun i j hij => by rw [g68n_EE J hsep, if_neg (Ne.symm hij)],
      g68n_Esum J hsep⟩⟩
  obtain ⟨t0⟩ := hne l
  set E := shapeProjector J l with hE
  have hEE : E * E = E := by rw [hE, g68n_EE J hsep, if_pos rfl]
  have hEF0 : E * jmSpectralProjector J ⟨l, t0⟩ = jmSpectralProjector J ⟨l, t0⟩ := by
    rw [hE, g68n_EF J hsep, if_pos rfl]
  have hEne : E ≠ 0 := by
    intro h; rw [h, zero_mul] at hEF0; exact g68n_F_ne J hsep _ hEF0.symm
  refine ⟨hEne, hEE, g68n_E_central J hsep l, fun p q hp hq hpp hqq hpq hqp he => ?_⟩
  -- p * E = p
  have hpE : p * E = p := by rw [he, mul_add, hpp, hpq, add_zero]
  -- p F_u = b_u F_u
  have hb : ∀ u : CellTableau Shape T, ∃ b : K,
      p * jmSpectralProjector J u = b • jmSpectralProjector J u := by
    intro u
    obtain ⟨b, hb⟩ := g68n_FxF_F J hsep u p
    refine ⟨b, ?_⟩
    rw [← hb, ← hp (jmSpectralProjector J u), mul_assoc, g67e_FF J hsep, if_pos rfl]
  choose b hbu using hb
  have hconst : ∀ u v : T l, b ⟨l, u⟩ = b ⟨l, v⟩ := by
    intro u v
    have h1 : p * seminormal J ⟨l, (u, v)⟩ = b ⟨l, u⟩ • seminormal J ⟨l, (u, v)⟩ := by
      have : seminormal J ⟨l, (u, v)⟩ = jmSpectralProjector J ⟨l, u⟩ * seminormal J ⟨l, (u, v)⟩ := by
        rw [g68n_Ff J hsep, if_pos rfl]
      conv_lhs => rw [this, ← mul_assoc, hbu, smul_mul_assoc, ← this]
    have h2 : seminormal J ⟨l, (u, v)⟩ * p = b ⟨l, v⟩ • seminormal J ⟨l, (u, v)⟩ := by
      have : seminormal J ⟨l, (u, v)⟩ = seminormal J ⟨l, (u, v)⟩ * jmSpectralProjector J ⟨l, v⟩ := by
        rw [g68n_fF J hsep, if_pos rfl]
      conv_lhs => rw [this, mul_assoc, ← hp (jmSpectralProjector J ⟨l, v⟩), hbu, mul_smul_comm, ← this]
    have h3 := hp (seminormal J ⟨l, (u, v)⟩)
    rw [h1, h2] at h3
    have := sub_eq_zero.mpr h3
    rw [← sub_smul] at this
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right (g68n_f_ne J _))
  have hpb : p = b ⟨l, t0⟩ • E := by
    rw [← hpE, hE, shapeProjector, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hbu, hconst t t0]
  have hb2 : b ⟨l, t0⟩ * b ⟨l, t0⟩ = b ⟨l, t0⟩ := by
    have h := hpp
    rw [hpb, smul_mul_smul_comm, hEE] at h
    have := sub_eq_zero.mpr h
    rw [← sub_smul] at this
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hEne)
  rcases g68n_idem_K hb2 with h0 | h0
  · left; rw [hpb, h0, zero_smul]
  · right
    have : q = E - p := by rw [he]; abel
    rw [this, hpb, h0, one_smul, sub_self]

end G68N4

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section G68N5
variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

lemma g68n_rI_eq (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (s t : T l) :
    rightIdealSpan (K := K) (seminormal J ⟨l, (s, t)⟩) =
      Submodule.span K (Set.range (fun v : T l => seminormal J ⟨l, (s, v)⟩)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    rw [g68n_fx J hsep]
    exact Submodule.sum_mem _ (fun v _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    refine Submodule.subset_span ⟨(seminormalGamma J ⟨l, t⟩)⁻¹ • seminormal J ⟨l, (t, v)⟩, ?_⟩
    rw [mul_smul_comm, g68n_mult J hsep, if_pos rfl, smul_smul,
      inv_mul_cancel₀ (g67e_gamma J hsep ⟨l, t⟩), one_smul]

lemma g68n_rI_mul (f : A) (y : A) (hy : y ∈ rightIdealSpan (K := K) f) (a : A) :
    y * a ∈ rightIdealSpan (K := K) f := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact Submodule.subset_span ⟨b * a, by rw [mul_assoc]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

lemma g68n_rI_I (J : JMFamily D M) (l : Shape) (s t : T l) (y : A)
    (hy : y ∈ rightIdealSpan (K := K) (seminormal J ⟨l, (s, t)⟩)) : y ∈ g68n_I D l := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact g68n_I_mul l _ (g68n_f_I J l s t) b
  | zero => simp
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ _ hx

lemma g68n_cellAct_eq (l : Shape) (s0 : T l) (v : T l → K) (x : A) :
    cellAct D l v x = fun u => ∑ t, v t * g68n_rho D l t x u := by
  unfold cellAct
  rw [dif_pos ⟨s0⟩]
  funext u
  refine Finset.sum_congr rfl (fun t _ => ?_)
  congr 1
  rw [g68n_K l _ (g68n_basis_I l _ t)]
  rw [Finset.sum_eq_single t]
  · rw [Module.Basis.repr_self, Finsupp.single_eq_same, one_mul]
  · intro w _ hw
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg, zero_mul]
    intro e
    have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
    simp only [Prod.mk.injEq] at this
    exact hw this.2.symm
  · simp

omit [Fintype Shape] [∀ l, Fintype (T l)] in
lemma g68n_td_same {l : Shape} {a b : T l}
    (h : tabDominates (⟨l, a⟩ : CellTableau Shape T) ⟨l, b⟩) : b ≤ a := by
  rcases h with h | ⟨l', s', t', e1, e2, hle⟩
  · exact absurd h (lt_irrefl _)
  · obtain ⟨rfl, e1'⟩ := Sigma.mk.inj_iff.mp e1
    obtain ⟨-, e2'⟩ := Sigma.mk.inj_iff.mp e2
    rw [eq_of_heq e1', eq_of_heq e2']; exact hle

lemma g68n_f_coef (J : JMFamily D M) (l : Shape) (s v w : T l) (hvw : v ≠ w) (hn : ¬ v < w) :
    D.basis.repr (seminormal J ⟨l, (s, v)⟩) ⟨l, (s, w)⟩ = 0 := by
  have h := g67d_Up_repr _ _ (g67d_semi_sub J ⟨l, (s, v)⟩) ⟨l, (s, w)⟩ (by
    rintro ⟨-, h2, -⟩
    exact hn (lt_of_le_of_ne (g68n_td_same h2) hvw))
  rw [map_sub, Finsupp.sub_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg, sub_zero] at h
  · exact h
  · intro e
    have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
    simp only [Prod.mk.injEq] at this
    exact hvw this.2

lemma g68n_row_inj (J : JMFamily D M) (l : Shape) (s : T l) (c : T l → K)
    (h : ∀ u, ∑ v, c v * D.basis.repr (seminormal J ⟨l, (s, v)⟩) ⟨l, (s, u)⟩ = 0) : c = 0 := by
  by_contra hne
  obtain ⟨v1, hv1⟩ := Function.ne_iff.mp hne
  obtain ⟨v0, hv0, hmin⟩ := (Finset.univ.filter (fun v => c v ≠ 0)).exists_minimal ⟨v1, by simpa using hv1⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv0 hmin
  have := h v0
  rw [Finset.sum_eq_single v0] at this
  · rw [g68n_f_one, mul_one] at this; exact hv0 this
  · intro v _ hv
    by_cases hcv : c v = 0
    · rw [hcv, zero_mul]
    · rw [g68n_f_coef J l s v v0 hv (fun hlt => (not_le_of_gt hlt) (hmin hcv hlt.le)), mul_zero]
  · simp

def g68n_Psi (l : Shape) (s : T l) (I : Submodule K A) : I →ₗ[K] (T l → K) where
  toFun y := fun u => D.basis.repr (y : A) ⟨l, (s, u)⟩
  map_add' x y := by funext u; simp
  map_smul' c x := by funext u; simp

theorem g68n_cell_right (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (s t : T l) :
    CellRightIso (D := D) l (rightIdealSpan (K := K) (seminormal J ⟨l, (s, t)⟩)) ∧
    rightIdealSpan (K := K) (seminormal J ⟨l, (s, t)⟩) =
      Submodule.span K (Set.range (fun v : T l => seminormal J ⟨l, (s, v)⟩)) := by
  refine ⟨?_, g68n_rI_eq J hsep l s t⟩
  set I := rightIdealSpan (K := K) (seminormal J ⟨l, (s, t)⟩) with hI
  set Ψ := g68n_Psi (D := D) l s I with hΨ
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : (y : A) ∈ Submodule.span K (Set.range (fun v : T l => seminormal J ⟨l, (s, v)⟩)) := by
      rw [← g68n_rI_eq J hsep l s t]; exact y.2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy'
    have hc0 : c = 0 := by
      apply g68n_row_inj J l s c
      intro u
      have := congrFun hy u
      simp only [hΨ, g68n_Psi, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      rw [← hc, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply] at this
      simpa [map_smul] using this
    apply Subtype.ext
    rw [← hc, hc0]; simp
  have hli : LinearIndependent K (fun v : T l => seminormal J ⟨l, (s, v)⟩) := by
    have := (g68n_fb J hsep).linearIndependent.comp (fun v : T l => (⟨l, (s, v)⟩ : CellIndex Shape T))
      (fun a b e => by
        have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
        simp only [Prod.mk.injEq] at this
        exact this.2)
    convert this using 1
    funext v; simp [g68n_fb_apply]
  have hdim : Module.finrank K I = Module.finrank K (T l → K) := by
    rw [hI, g68n_rI_eq J hsep l s t, finrank_span_eq_card hli, Module.finrank_fintype_fun_eq_card]
  haveI : FiniteDimensional K A := Module.Finite.of_basis D.basis
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  have hequiv : ∀ (y : I) (a : A), Ψ ⟨(y : A) * a, g68n_rI_mul _ _ y.2 a⟩ = cellAct D l (Ψ y) a := by
    intro y a
    rw [g68n_cellAct_eq l s]
    funext u
    simp only [hΨ, g68n_Psi, LinearMap.coe_mk, AddHom.coe_mk]
    exact g68n_K l _ (g68n_rI_I J l s t _ y.2) a s u
  let e := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm
  refine ⟨e, fun v a => ?_⟩
  have h1 : Ψ (e v) = v := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).apply_symm_apply v
  have h2 := hequiv (e v) a
  rw [h1] at h2
  have h3 : e (cellAct D l v a) = ⟨((e v : I) : A) * a, g68n_rI_mul _ _ (e v).2 a⟩ := by
    rw [← h2]
    exact (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm_apply_apply _
  rw [h3]

end G68N5

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section G68N6
variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

lemma g68n_Irepr {m l : Shape} (h : ¬ m ≤ l) (p : T l × T l) (z : A) (hz : z ∈ g68n_I D m) :
    D.basis.repr z ⟨l, p⟩ = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, hw, rfl⟩ := hz
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg]
    intro e
    have : w.1 = l := congrArg Sigma.fst e
    rw [this] at hw
    exact h hw
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

lemma g68n_rho_eq (l : Shape) (x t : T l) (Y : A) (y : T l) :
    g68n_rho D l t Y y = D.basis.repr (D.basis ⟨l, (x, t)⟩ * Y) ⟨l, (x, y)⟩ := by
  rw [g68n_K l _ (g68n_basis_I l x t), Finset.sum_eq_single t]
  · rw [Module.Basis.repr_self, Finsupp.single_eq_same, one_mul]
  · intro w _ hw
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg, zero_mul]
    intro e
    have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
    simp only [Prod.mk.injEq] at this
    exact hw this.2.symm
  · simp

lemma g68n_col (l : Shape) (Z : A) (hZ : Z ∈ g68n_I D l) (u y x y' : T l) :
    D.basis.repr (Z * D.basis ⟨l, (u, y)⟩) ⟨l, (x, y')⟩ =
      if y' = y then g68n_rho D l u (D.star Z) x else 0 := by
  rw [← g68n_repr_star, D.star_mul, D.star_basis, g68n_K l _ (g68n_basis_I l y u)]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single u]
    · rw [Module.Basis.repr_self, Finsupp.single_eq_same, one_mul]
    · intro w _ hw
      rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg, zero_mul]
      intro e
      have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
      simp only [Prod.mk.injEq] at this
      exact hw this.2.symm
    · simp
  · refine Finset.sum_eq_zero (fun w _ => ?_)
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg, zero_mul]
    intro e
    have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
    simp only [Prod.mk.injEq] at this
    exact h this.1.symm

lemma g68n_rho_basis (l : Shape) (t u y y' : T l) :
    g68n_rho D l t (D.basis ⟨l, (u, y)⟩) y' = if y' = y then gramEntry D l t u else 0 := by
  have key : ∀ x y : T l, g68n_rho D l t (D.basis ⟨l, (u, y)⟩) y =
      g68n_rho D l u (D.basis ⟨l, (t, x)⟩) x := by
    intro x y
    rw [g68n_rho_eq l x t, g68n_col l _ (g68n_basis_I l x t), if_pos rfl, D.star_basis]
  rw [g68n_rho_eq l t t, g68n_col l _ (g68n_basis_I l t t), D.star_basis]
  split_ifs with h
  · subst h
    unfold gramEntry
    rw [← g68n_rho_eq l t t]; exact (key t t).symm
  · rfl

lemma g68n_act_basis (l : Shape) (s0 : T l) (v : T l → K) (u y : T l) :
    cellAct D l v (D.basis ⟨l, (u, y)⟩) =
      fun y' => if y' = y then ∑ t, v t * gramEntry D l t u else 0 := by
  rw [g68n_cellAct_eq l s0]
  funext y'
  simp_rw [g68n_rho_basis]
  split_ifs <;> simp

lemma g68n_form_e (l : Shape) (v : T l → K) (u : T l) :
    cellForm D l v (cellVector l u) = ∑ t, v t * gramEntry D l t u := by
  unfold cellForm cellVector
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_eq_single u]
  · simp
  · intro w _ hw; simp [hw]
  · simp

lemma g68n_span_coef (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (s : T l) (y : A)
    (hy : y ∈ rightIdealSpan (K := K) (seminormal J ⟨l, (s, s)⟩)) :
    ∃ c : T l → K, y = ∑ v, c v • seminormal J ⟨l, (s, v)⟩ := by
  rw [g68n_rI_eq J hsep] at hy
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
  exact ⟨c, hc.symm⟩

lemma g68n_y_f (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (s : T l) (c : T l → K)
    (w u : T l) :
    (∑ v, c v • seminormal J ⟨l, (s, v)⟩) * seminormal J ⟨l, (w, u)⟩ =
      (c w * seminormalGamma J ⟨l, w⟩) • seminormal J ⟨l, (s, u)⟩ := by
  rw [Finset.sum_mul, Finset.sum_eq_single w]
  · rw [smul_mul_assoc, g68n_mult J hsep, if_pos rfl, smul_smul]
  · intro v _ hv; rw [smul_mul_assoc, g68n_mult J hsep, if_neg hv, smul_zero]
  · simp

theorem g68n_radical (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) :
    ZeroCellRadical D l := by
  intro v hv
  by_cases hne : Nonempty (T l)
  swap
  · funext t; exact absurd ⟨t⟩ hne
  obtain ⟨s⟩ := hne
  obtain ⟨⟨e, he⟩, -⟩ := g68n_cell_right J hsep l s s
  have hact : ∀ u y : T l, cellAct D l v (D.basis ⟨l, (u, y)⟩) = 0 := by
    intro u y
    rw [g68n_act_basis l s]
    funext y'
    have := hv (cellVector l u)
    rw [g68n_form_e] at this
    simp [this]
  set y : A := (e v : A) with hydef
  have hyI : y ∈ rightIdealSpan (K := K) (seminormal J ⟨l, (s, s)⟩) := (e v).2
  obtain ⟨c, hc⟩ := g68n_span_coef J hsep l s y hyI
  -- y kills I_l
  have hgen : ∀ z : CellIndex Shape T, l ≤ z.1 → y * D.basis z = 0 := by
    rintro ⟨m, u, y'⟩ hlm
    rcases eq_or_lt_of_le hlm with h | h
    · subst h
      rw [hydef, ← he, hact, map_zero]; rfl
    · have h1 : y * D.basis ⟨m, (u, y')⟩ ∈ rightIdealSpan (K := K) (seminormal J ⟨l, (s, s)⟩) :=
        g68n_rI_mul _ _ hyI _
      obtain ⟨d, hd⟩ := g68n_span_coef J hsep l s _ h1
      have h2 : y * D.basis ⟨m, (u, y')⟩ ∈ g68n_I D m :=
        g68n_I_lmul m _ (Submodule.subset_span ⟨⟨m, (u, y')⟩, le_rfl, rfl⟩) y
      have hd0 : d = 0 := by
        apply g68n_row_inj J l s d
        intro u'
        have := g68n_Irepr (not_le_of_gt h) (s, u') _ h2
        rw [hd, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply] at this
        simpa [map_smul] using this
      rw [hd, hd0]; simp
  have hkill : ∀ x ∈ g68n_I D l, y * x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨z, hz, rfl⟩ := hx; exact hgen z hz
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
    | smul k a _ ha => rw [mul_smul_comm, ha, smul_zero]
  have hc0 : c = 0 := by
    funext w
    have := hkill _ (g68n_f_I J l w w)
    rw [hc, g68n_y_f J hsep] at this
    have := (smul_eq_zero.mp this).resolve_right (g68n_f_ne J _)
    exact (mul_eq_zero.mp this).resolve_right (g67e_gamma J hsep _)
  have : e v = 0 := by
    apply Subtype.ext
    show y = 0
    rw [hc, hc0]; simp
  exact (map_eq_zero_iff e e.injective).mp this

theorem g68n_irred (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (hne : Nonempty (T l)) :
    IrreducibleCell D l := by
  obtain ⟨s⟩ := hne
  refine ⟨⟨cellVector l s, fun h => by
    have := congrFun h s
    simp [cellVector] at this⟩, fun S hS => ?_⟩
  by_cases hS0 : S = ⊥
  · exact Or.inl hS0
  right
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  obtain ⟨⟨e, he⟩, -⟩ := g68n_cell_right J hsep l s s
  obtain ⟨c, hc⟩ := g68n_span_coef J hsep l s _ (e v).2
  have hc0 : c ≠ 0 := by
    intro h
    apply hv0
    have : e v = 0 := Subtype.ext (by rw [hc, h]; simp)
    exact (map_eq_zero_iff e e.injective).mp this
  obtain ⟨w0, hw0⟩ := Function.ne_iff.mp hc0
  set k := c w0 * seminormalGamma J ⟨l, w0⟩ with hk
  have hk0 : k ≠ 0 := mul_ne_zero hw0 (g67e_gamma J hsep _)
  -- each f_su is e of an element of S
  have hf : ∀ u : T l, ∃ x ∈ S, (e x : A) = seminormal J ⟨l, (s, u)⟩ := by
    intro u
    refine ⟨k⁻¹ • cellAct D l v (seminormal J ⟨l, (w0, u)⟩),
      S.smul_mem _ (hS v hvS _), ?_⟩
    rw [map_smul, Submodule.coe_smul, he, hc, g68n_y_f J hsep, ← hk, smul_smul,
      inv_mul_cancel₀ hk0, one_smul]
  choose x hxS hx using hf
  rw [eq_top_iff]
  intro v' _
  obtain ⟨d, hd⟩ := g68n_span_coef J hsep l s _ (e v').2
  have : v' = ∑ u, d u • x u := by
    apply e.injective
    apply Subtype.ext
    rw [hd, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [map_smul, Submodule.coe_smul, hx]
  rw [this]
  exact S.sum_mem (fun u _ => S.smul_mem _ (hxS u))

end G68N6

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section G68N7
variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

def g68n_Phi (J : JMFamily D M) : A →ₗ[K] (∀ r : CellTableau Shape T, T r.1 → K) where
  toFun x := fun r u => D.basis.repr (jmSpectralProjector J r * x) ⟨r.1, (r.2, u)⟩
  map_add' x y := by funext r u; simp [mul_add]
  map_smul' c x := by funext r u; simp [mul_smul_comm]

lemma g68n_F_I (J : JMFamily D M) (hsep : separatesAll J) (r : CellTableau Shape T) :
    jmSpectralProjector J r ∈ g68n_I D r.1 := by
  rw [g68n_F_gam J hsep r]
  exact Submodule.smul_mem _ _ (g68n_f_I J r.1 r.2 r.2)

theorem g68n_regular (J : JMFamily D M) (hsep : separatesAll J) :
    (∀ l, ZeroCellRadical D l) ∧
    ∃ e : A ≃ₗ[K] (∀ r : CellTableau Shape T, T r.1 → K),
      ∀ x a r, e (x * a) r = cellAct D r.1 (e x r) a := by
  refine ⟨fun l => g68n_radical J hsep l, ?_⟩
  set Φ := g68n_Phi J with hΦ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hr : ∀ r : CellTableau Shape T, jmSpectralProjector J r * x = 0 := by
      rintro ⟨l, s⟩
      have hmem : jmSpectralProjector J ⟨l, s⟩ * x ∈
          rightIdealSpan (K := K) (seminormal J ⟨l, (s, s)⟩) := by
        rw [g68n_F_gam J hsep, smul_mul_assoc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
      obtain ⟨c, hc⟩ := g68n_span_coef J hsep l s _ hmem
      have hc0 : c = 0 := by
        apply g68n_row_inj J l s c
        intro u
        have := congrFun (congrFun hx ⟨l, s⟩) u
        simp only [hΦ, g68n_Phi, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
        rw [hc, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply] at this
        simpa [map_smul] using this
      rw [hc, hc0]; simp
    rw [← one_mul x, ← g68n_Fsum J hsep, Finset.sum_mul]
    exact Finset.sum_eq_zero (fun r _ => hr r)
  haveI : FiniteDimensional K A := Module.Finite.of_basis D.basis
  have hdim : Module.finrank K A = Module.finrank K (∀ r : CellTableau Shape T, T r.1 → K) := by
    rw [Module.finrank_eq_card_basis D.basis, Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card]
    rw [Fintype.sum_sigma, Fintype.card_sigma]
    simp only [Fintype.card_prod]
    refine Finset.sum_congr rfl (fun l _ => ?_); symm
    show ∑ _x : T l, Fintype.card (T l) = _
    simp
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun x a r => ?_⟩
  simp only [LinearEquiv.ofBijective_apply, hΦ, g68n_Phi, LinearMap.coe_mk, AddHom.coe_mk]
  rw [g68n_cellAct_eq r.1 r.2]
  funext u
  rw [← mul_assoc]
  exact g68n_K r.1 _ (g68n_I_mul r.1 _ (g68n_F_I J hsep r) x) a r.2 u

end G68N7

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section G68N8
variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

lemma g68n_rhoQ (l : Shape) (t' y : T l) (Q : A) (hQ : Q ∈ g68n_I D l) :
    D.basis.repr (D.basis ⟨l, (t', t')⟩ * Q) ⟨l, (t', y)⟩ =
      ∑ u', gramEntry D l t' u' * D.basis.repr Q ⟨l, (u', y)⟩ := by
  induction hQ using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨⟨m, u'', y''⟩, hlm, rfl⟩ := hQ
    rcases eq_or_lt_of_le hlm with h | h
    · subst h
      rw [← g68n_rho_eq l t' t', g68n_rho_basis, Finset.sum_eq_single u'']
      · rw [Module.Basis.repr_self, Finsupp.single_apply]
        by_cases hy : y = y''
        · subst hy; simp
        · rw [if_neg hy, if_neg, mul_zero]
          intro e
          have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
          simp only [Prod.mk.injEq] at this
          exact hy this.2.symm
      · intro w _ hw
        rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg, mul_zero]
        intro e
        have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
        simp only [Prod.mk.injEq] at this
        exact hw this.1.symm
      · simp
    · have hb : D.basis ⟨m, (u'', y'')⟩ ∈ g68n_I D m :=
        Submodule.subset_span ⟨⟨m, (u'', y'')⟩, le_rfl, rfl⟩
      have h1 := g68n_Irepr (D := D) (not_le_of_gt h) (t', y) _
        (g68n_I_lmul m _ hb (D.basis ⟨l, (t', t')⟩))
      rw [h1]
      symm
      refine Finset.sum_eq_zero (fun w _ => ?_)
      rw [g68n_Irepr (D := D) (not_le_of_gt h) (w, y) _ hb, mul_zero]
  | zero => simp
  | add x x' _ _ hx hx' =>
    rw [mul_add, map_add, Finsupp.add_apply, hx, hx', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [map_add, Finsupp.add_apply, mul_add]
  | smul c x _ hx =>
    rw [mul_smul_comm, map_smul, Finsupp.smul_apply, hx, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring

lemma g68n_formPQ (l : Shape) (P Q : A) (hP : P ∈ g68n_I D l) (hQ : Q ∈ g68n_I D l) (x y : T l) :
    D.basis.repr (P * Q) ⟨l, (x, y)⟩ =
      cellForm D l (fun t' => D.basis.repr P ⟨l, (x, t')⟩) (fun u' => D.basis.repr Q ⟨l, (u', y)⟩) := by
  rw [g68n_K l P hP Q x y]
  unfold cellForm
  refine Finset.sum_congr rfl (fun t' _ => ?_)
  rw [g68n_rho_eq l t' t', g68n_rhoQ l t' y Q hQ, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u' _ => ?_)
  ring

lemma g68n_sv (J : JMFamily D M) (l : Shape) (s t : T l) :
    seminormalVector J l t = fun u => D.basis.repr (seminormal J ⟨l, (s, t)⟩) ⟨l, (s, u)⟩ := by
  unfold seminormalVector
  rw [g68n_cellAct_eq l t]
  funext u
  rw [g68n_f_row, Finset.sum_eq_single t]
  · simp [cellVector]
  · intro w _ hw; simp [cellVector, hw]
  · simp

lemma g68n_form_sv (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) (t u : T l) :
    cellForm D l (seminormalVector J l t) (seminormalVector J l u) =
      if t = u then seminormalGamma J ⟨l, t⟩ else 0 := by
  have h := g68n_formPQ l _ _ (g68n_f_I J l t t) (g68n_f_I J l u u) t u
  have hQ : (fun u' => D.basis.repr (seminormal J ⟨l, (u, u)⟩) ⟨l, (u', u)⟩) =
      seminormalVector J l u := by
    rw [g68n_sv J l u u]
    funext u'
    rw [← g68n_repr_star, g68n_star_f J hsep]
  rw [hQ, ← g68n_sv J l t t, g68n_mult J hsep] at h
  rw [← h]
  split_ifs with htu
  · subst htu
    rw [map_smul, Finsupp.smul_apply, g68n_f_one, smul_eq_mul, mul_one]
  · simp

lemma g68n_sb (J : JMFamily D M) (hsep : separatesAll J) (z : CellIndex Shape T) :
    seminormalBasis J z = seminormal J z := by
  have h : ∃ b : Module.Basis (CellIndex Shape T) K A, ∀ z, b z = seminormal J z :=
    ⟨g68n_fb J hsep, g68n_fb_apply J hsep⟩
  unfold seminormalBasis
  rw [dif_pos h]
  exact Classical.choose_spec h z

lemma g68n_sb_repr (J : JMFamily D M) (hsep : separatesAll J) (z : CellIndex Shape T) :
    (seminormalBasis J).repr (seminormal J z) = Finsupp.single z 1 := by
  rw [← g68n_sb J hsep, Module.Basis.repr_self]

lemma g68n_ext_form (J : JMFamily D M) (hsep : separatesAll J) (z w : CellIndex Shape T) :
    extendedForm J (seminormal J z) (seminormal J w) =
      if z = w then seminormalGamma J ⟨z.1, z.2.2⟩ else 0 := by
  obtain ⟨l, s, t⟩ := z
  unfold extendedForm
  simp only [g68n_sb_repr J hsep]
  rw [Finset.sum_eq_single l, Finset.sum_eq_single s, Finset.sum_eq_single t]
  · simp only [Finsupp.single_eq_same, one_mul]
    obtain ⟨m, s', u⟩ := w
    by_cases hm : m = l
    · subst hm
      by_cases hs : s' = s
      · subst hs
        rw [Finset.sum_eq_single u]
        · rw [Finsupp.single_eq_same, one_mul, g68n_form_sv J hsep]
          by_cases htu : t = u
          · subst htu; simp
          · rw [if_neg htu, if_neg]
            intro e
            have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
            simp only [Prod.mk.injEq] at this
            exact htu this.2
        · intro v _ hv
          rw [Finsupp.single_apply, if_neg, zero_mul]
          intro e
          have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
          simp only [Prod.mk.injEq] at this
          exact hv this.2.symm
        · simp
      · rw [if_neg]
        · refine Finset.sum_eq_zero (fun v _ => ?_)
          rw [Finsupp.single_apply, if_neg, zero_mul]
          intro e
          have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
          simp only [Prod.mk.injEq] at this
          exact hs this.1
        · intro e
          have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
          simp only [Prod.mk.injEq] at this
          exact hs this.1.symm
    · rw [if_neg]
      · refine Finset.sum_eq_zero (fun v _ => ?_)
        rw [Finsupp.single_apply, if_neg, zero_mul]
        intro e
        exact hm (congrArg Sigma.fst e)
      · intro e
        exact hm (congrArg Sigma.fst e).symm
  all_goals first
    | (intro b _ hb
       refine Finset.sum_eq_zero (fun v _ => ?_)
       rw [Finsupp.single_apply, if_neg, zero_mul, zero_mul]
       intro e
       have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
       simp only [Prod.mk.injEq] at this
       exact hb this.2.symm)
    | (intro b _ hb
       refine Finset.sum_eq_zero (fun t' _ => Finset.sum_eq_zero (fun v _ => ?_))
       rw [Finsupp.single_apply, if_neg, zero_mul, zero_mul]
       intro e
       have := eq_of_heq (Sigma.mk.inj_iff.mp e).2
       simp only [Prod.mk.injEq] at this
       exact hb this.1.symm)
    | (intro b _ hb
       refine Finset.sum_eq_zero (fun s' _ => Finset.sum_eq_zero (fun t' _ =>
         Finset.sum_eq_zero (fun v _ => ?_)))
       rw [Finsupp.single_apply, if_neg, zero_mul, zero_mul]
       intro e
       exact hb (congrArg Sigma.fst e).symm)
    | simp

theorem g68n_semiorth (J : JMFamily D M) (hsep : separatesAll J) :
    (∃ b : Module.Basis (CellIndex Shape T) K A, ∀ z, b z = seminormal J z) ∧
    (∀ z w : CellIndex Shape T, z ≠ w →
      extendedForm J (seminormal J z) (seminormal J w) = 0) ∧
    (∀ z : CellIndex Shape T, extendedForm J (seminormal J z) (seminormal J z) ≠ 0) := by
  refine ⟨⟨g68n_fb J hsep, g68n_fb_apply J hsep⟩, fun z w h => ?_, fun z => ?_⟩
  · rw [g68n_ext_form J hsep, if_neg h]
  · rw [g68n_ext_form J hsep, if_pos rfl]
    exact g67e_gamma J hsep _

end G68N8

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section G68N9
variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

lemma g68n_S_zero (J : JMFamily D M) (l : Shape) (t u : T l) (h : t ≠ u) (hn : ¬ t < u) :
    seminormalVector J l t u = 0 := by
  rw [g68n_sv J l t t]
  exact g68n_f_coef J l t t u h hn

lemma g68n_S_one (J : JMFamily D M) (l : Shape) (t : T l) :
    seminormalVector J l t t = 1 := by
  rw [g68n_sv J l t t]
  exact g68n_f_one J _

lemma g68n_detS (J : JMFamily D M) (l : Shape) :
    Matrix.det (fun t u : T l => seminormalVector J l t u) = 1 := by
  set S : Matrix (T l) (T l) K := fun t u => seminormalVector J l t u with hS
  have hBT : S.BlockTriangular (fun t : T l => g67e_pos t) := by
    intro t u hlt
    show seminormalVector J l t u = 0
    apply g68n_S_zero J l t u
    · rintro rfl; exact lt_irrefl _ hlt
    · intro htu; exact absurd (g67e_pos_lt htu) (not_lt_of_gt hlt)
  rw [hBT.det]
  refine Finset.prod_eq_one (fun a _ => ?_)
  have : S.toSquareBlock (fun t : T l => g67e_pos t) a = 1 := by
    ext i j
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply]
    split_ifs with hij
    · subst hij; exact g68n_S_one J l _
    · apply g68n_S_zero J l
      · intro e; exact hij (Subtype.ext e)
      · intro hlt
        have := g67e_pos_lt hlt
        rw [i.2, j.2] at this
        exact lt_irrefl _ this
  rw [this, Matrix.det_one]

theorem g68n_gram (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) :
    gramDet D l = ∏ t : T l, seminormalGamma J ⟨l, t⟩ := by
  set S : Matrix (T l) (T l) K := fun t u => seminormalVector J l t u with hS
  set G : Matrix (T l) (T l) K := gramEntry D l with hG
  have hprod : S * G * S.transpose = Matrix.diagonal (fun t => seminormalGamma J ⟨l, t⟩) := by
    ext t u
    have h := g68n_form_sv J hsep l t u
    unfold cellForm at h
    rw [Matrix.diagonal_apply, ← h]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t' _ => Finset.sum_congr rfl (fun u' _ => ?_))
    simp only [hS, hG]; ring
  have h2 := congrArg Matrix.det hprod
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h2
  have h1 : S.det = 1 := g68n_detS J l
  rw [h1, one_mul, mul_one] at h2
  exact h2

end G68N9

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section G68N10
variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

lemma g68n_univ_map {α : Type*} {n : ℕ} (f : Fin n → α) :
    (Finset.univ : Finset (Fin n)).val.map f = (List.ofFn f : Multiset α) := by
  simp [Fin.univ_def, List.ofFn_eq_map]

lemma g68n_central_add {x y : A} (hx : Central x) (hy : Central y) : Central (x + y) := by
  intro a; rw [add_mul, mul_add, hx a, hy a]

lemma g68n_central_sum {ι : Type*} (s : Finset ι) (f : ι → A) (h : ∀ i ∈ s, Central (f i)) :
    Central (∑ i ∈ s, f i) := by
  intro a
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi => h i hi a)

lemma g68n_central_shape (J : JMFamily D M) (hsep : separatesAll J) (a : CellTableau Shape T → K)
    (ha : ∀ l (s t : T l), a ⟨l, s⟩ = a ⟨l, t⟩) :
    Central (∑ t, a t • jmSpectralProjector J t) := by
  rw [Fintype.sum_sigma]
  refine g68n_central_sum _ _ (fun l _ => ?_)
  by_cases hne : Nonempty (T l)
  · obtain ⟨s0⟩ := hne
    have : ∑ s : T l, a ⟨l, s⟩ • jmSpectralProjector J ⟨l, s⟩ = a ⟨l, s0⟩ • shapeProjector J l := by
      rw [shapeProjector, Finset.smul_sum]
      exact Finset.sum_congr rfl (fun s _ => by rw [ha l s s0])
    rw [this]
    intro b
    rw [smul_mul_assoc, mul_smul_comm, g68n_E_central J hsep l b]
  · have : ∑ s : T l, a ⟨l, s⟩ • jmSpectralProjector J ⟨l, s⟩ = 0 := by
      apply Finset.sum_eq_zero; intro s; exact absurd ⟨s⟩ hne
    rw [this]; intro b; simp

lemma g68n_polyeval {R : Type*} [CommRing R] [Algebra R K] [Algebra R A] [IsScalarTower R K A]
    (J : JMFamily D M) (hsep : separatesAll J) (P : MvPolynomial (Fin M) R) :
    ∑ m ∈ P.support, algebraMap R A (P.coeff m) * (List.ofFn fun i => J.L i ^ m i).prod =
      ∑ t, MvPolynomial.aeval (J.content t) P • jmSpectralProjector J t := by
  let b : jmAlgebra J :=
    ∑ m ∈ P.support, algebraMap K (jmAlgebra J) (algebraMap R K (P.coeff m)) *
      (List.ofFn fun i => jmGenerator J i ^ m i).prod -
    ∑ t, MvPolynomial.aeval (J.content t) P • g67e_Fb J t
  have hb : (b : A) = ∑ m ∈ P.support, algebraMap R A (P.coeff m) *
      (List.ofFn fun i => J.L i ^ m i).prod -
      ∑ t, MvPolynomial.aeval (J.content t) P • jmSpectralProjector J t := by
    have hv : ∀ y : jmAlgebra J, (y : A) = (jmAlgebra J).val y := fun _ => rfl
    rw [hv, map_sub, map_sum, map_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [map_mul, AlgHom.commutes, ← IsScalarTower.algebraMap_apply, map_list_prod, List.map_ofFn]
      congr 2
    · refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [map_smul, ← hv, g67e_Fb_coe]
  have := g67e_ss J hsep (b : A) b.2 (fun z => by
    rw [← g67e_chiZ_apply]
    simp only [b, map_sub, map_sum, map_mul, map_smul, AlgHom.commutes, g67e_chi_Fb J hsep,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      map_list_prod, List.map_ofFn]
    rw [sub_eq_zero, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    congr 1
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [Function.comp_apply, map_pow, g67e_chi_gen])
  rw [hb, sub_eq_zero] at this
  exact this

end G68N10

open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

section ResidueIntegrality

variable {R K AR AK Shape : Type*} [CommRing R] [modularDomain : IsDomain R]

variable [modularDVR : IsDiscreteValuationRing R] [Field K] [Algebra R K] [modularFraction : IsFractionRing R K]

variable [Ring AR] [Algebra R AR] [Ring AK] [Algebra K AK] [Algebra R AK]

variable [modularTower : IsScalarTower R K AK] [Fintype Shape] [PartialOrder Shape]

variable {T : Shape → Type*} [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]

variable {B : Type*} [Ring B] [Algebra (IsLocalRing.ResidueField R) B] {M : ℕ}

section ModularStatements

include modularDomain modularDVR modularFraction modularTower

/-- Proposition 4.13, PDF pp.20–21. Braces mean MULTISETS: the proof
requires equality under every symmetric polynomial, and equality of supports
would be false. Constancy of the multiset within each shape is equivalent to
the source's existential c_lambda list, including empty cells. Centrality is
a conclusion for EVERY symmetric polynomial over the residue field.
Uses corrected complete content-sequence separation. -/
theorem solution
    (S : ModularSystem (R := R) (K := K) (AR := AR) (AK := AK) (T := T) B M)
    (hsep : separatesAll S.integralJM)
    (hcontent : ∀ l (s t : T l),
      (List.ofFn (S.integralJM.content ⟨l, s⟩) : Multiset R) =
      (List.ofFn (S.integralJM.content ⟨l, t⟩) : Multiset R))
    (p : MvPolynomial (Fin M) (IsLocalRing.ResidueField R))
    (hsym : SymmetricPolynomial p) :
    Central (orderedPolynomialEval p (fun i => S.reduction (S.integralJM.L i))) := by
  set k := IsLocalRing.ResidueField R
  -- separation of the generic family
  have hinjRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hsepK : separatesAll S.genericJM := by
    intro t u htu
    apply hsep
    funext i
    apply hinjRK
    rw [S.inclusion_content, S.inclusion_content]
    exact congrFun htu i
  -- step 1: p is a polynomial in elementary symmetric polynomials
  have hsymm' : p ∈ MvPolynomial.symmetricSubalgebra (Fin M) k := fun e => hsym e
  obtain ⟨qb, hqb⟩ := MvPolynomial.esymmAlgHom_fin_surjective k (m := M) (n := M) le_rfl ⟨p, hsymm'⟩
  have hp : MvPolynomial.aeval (fun i : Fin M => MvPolynomial.esymm (Fin M) k (i + 1)) qb = p := by
    have := congrArg (MvPolynomial.symmetricSubalgebra (Fin M) k).val hqb
    simp only [MvPolynomial.esymmAlgHom, MvPolynomial.comp_aeval_apply] at this
    exact this
  obtain ⟨qR, hqR⟩ := MvPolynomial.map_surjective (IsLocalRing.residue R)
    IsLocalRing.residue_surjective qb
  set P : MvPolynomial (Fin M) R :=
    MvPolynomial.aeval (fun i : Fin M => MvPolynomial.esymm (Fin M) R (i + 1)) qR with hPdef
  have hPp : MvPolynomial.map (IsLocalRing.residue R) P = p := by
    rw [← hp, ← hqR, hPdef]
    have h1 : ∀ (g : Fin M → MvPolynomial (Fin M) R) (q : MvPolynomial (Fin M) R),
        MvPolynomial.aeval g q = MvPolynomial.bind₁ g q := fun g q => rfl
    rw [h1, MvPolynomial.map_bind₁]
    simp only [MvPolynomial.map_esymm]
    rfl
  -- step 2: the integral element
  set x : AR := orderedPolynomialEval P (fun i => S.integralJM.L i) with hx
  have hred : S.reduction x = orderedPolynomialEval p (fun i => S.reduction (S.integralJM.L i)) := by
    rw [hx, ← hPp]
    unfold orderedPolynomialEval
    rw [map_sum]
    symm
    have hterm : ∀ m : Fin M →₀ ℕ, S.reduction (algebraMap R AR (P.coeff m) *
        (List.ofFn fun i => S.integralJM.L i ^ m i).prod) =
        algebraMap k B ((MvPolynomial.map (IsLocalRing.residue R) P).coeff m) *
        (List.ofFn fun i => S.reduction (S.integralJM.L i) ^ m i).prod := by
      intro m
      rw [map_mul, S.reduction_scalars, MvPolynomial.coeff_map, map_list_prod, List.map_ofFn]
      simp only [Function.comp_def, map_pow]
      rfl
    rw [Finset.sum_congr rfl (fun m _ => hterm m)]
    refine Finset.sum_subset (MvPolynomial.support_map_subset _ _) (fun m _ hm => ?_)
    rw [MvPolynomial.notMem_support_iff] at hm
    rw [hm, map_zero, zero_mul]
  -- inclusion is injective
  have hrepr : ∀ (y : AR) (z : QAlgorithms.Papers.Independent.Renew46.P16.CellIndex Shape T),
      S.generic.basis.repr (S.inclusion y) z = algebraMap R K (S.integral.basis.repr y z) := by
    intro y z
    conv_lhs => rw [← S.integral.basis.sum_repr y]
    rw [map_sum, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single z]
    · rw [map_smul, S.inclusion_basis, ← algebraMap_smul K, map_smul, Module.Basis.repr_self]
      simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    · intro w _ hw
      rw [map_smul, S.inclusion_basis, ← algebraMap_smul K, map_smul, Module.Basis.repr_self]
      simp [Finsupp.single_apply, hw]
    · simp
  have hincinj : Function.Injective S.inclusion := by
    intro y y' hyy
    apply S.integral.basis.repr.injective
    ext z
    apply hinjRK
    rw [← hrepr, ← hrepr, hyy]
  -- generic computation
  have hinc : S.inclusion x = ∑ t, MvPolynomial.aeval (S.genericJM.content t) P •
      jmSpectralProjector S.genericJM t := by
    rw [← g68n_polyeval S.genericJM hsepK P, hx]
    unfold orderedPolynomialEval
    rw [map_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [map_mul, AlgHom.commutes, map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, map_pow, S.inclusion_jm]
  have hconst : ∀ l (s t : T l), MvPolynomial.aeval (S.genericJM.content ⟨l, s⟩) P =
      MvPolynomial.aeval (S.genericJM.content ⟨l, t⟩) P := by
    intro l s t
    have hev : ∀ u : T l, MvPolynomial.aeval (S.genericJM.content ⟨l, u⟩) P =
        MvPolynomial.aeval (fun i : Fin M => (((List.ofFn (S.integralJM.content ⟨l, u⟩) : Multiset R)).map
          (algebraMap R K)).esymm (i + 1)) qR := by
      intro u
      rw [hPdef, MvPolynomial.comp_aeval_apply]
      refine congrArg (fun g => MvPolynomial.aeval g qR) (funext fun i => ?_)
      rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, ← g68n_univ_map, Multiset.map_map]
      congr 2
      funext j
      simp only [Function.comp_apply, S.inclusion_content]
    rw [hev s, hev t, hcontent l s t]
  have hcK : Central (S.inclusion x) := by
    rw [hinc]
    exact g68n_central_shape S.genericJM hsepK _ hconst
  have hcR : Central x := by
    intro a
    apply hincinj
    rw [map_mul, map_mul, hcK]
  -- reduction is surjective
  have hsurj : Function.Surjective S.reduction := by
    intro b0
    refine ⟨∑ z, algebraMap R AR (Classical.choose (IsLocalRing.residue_surjective
      (S.special.basis.repr b0 z))) * S.integral.basis z, ?_⟩
    rw [map_sum]
    conv_rhs => rw [← S.special.basis.sum_repr b0]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [map_mul, S.reduction_scalars, S.reduction_basis,
      Classical.choose_spec (IsLocalRing.residue_surjective (S.special.basis.repr b0 z)),
      Algebra.smul_def]
  rw [← hred]
  intro b0
  obtain ⟨a, rfl⟩ := hsurj b0
  rw [← map_mul, ← map_mul, hcR]

end ModularStatements

end ResidueIntegrality

end
