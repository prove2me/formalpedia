-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P08.jm_irreducible_characters
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:41:41.414175+00:00
-- url     : https://prove2.me/submissions/e72fa832-d7ed-44bd-b9b1-848f2e44882b

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

end G67EJ

section SeparatedDefinitions

variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]

variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}

variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]

variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

theorem solution (J : JMFamily D M) :
    (∀ a b : jmAlgebra J, a * b = b * a) ∧
    ∃ chi : CellTableau Shape T → (jmAlgebra J →ₐ[K] K),
      (∀ t i, chi t (jmGenerator J i) = J.content t i) ∧
      (∀ (V : Type*) [AddCommGroup V] [Module K V]
        (rho : jmAlgebra J →ₐ[K] Module.End K V),
        IrreducibleRepresentation rho →
        ∃ t : CellTableau Shape T, ∃ e : V ≃ₗ[K] K,
          ∀ a v, e (rho a v) = chi t a * e v) := g67e_main J

end SeparatedDefinitions

end
