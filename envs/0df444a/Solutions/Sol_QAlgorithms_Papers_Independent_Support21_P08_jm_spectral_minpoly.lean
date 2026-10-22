-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P08.jm_spectral_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:27:58.714907+00:00
-- url     : https://prove2.me/submissions/5702ddec-1932-47db-9fc8-b831f196c0ed

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

section SeparatedDefinitions

variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]

variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}

variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]

variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

theorem solution (J : JMFamily D M) (hsep : separatesAll J) (i : Fin M) :
    J.L i = ∑ t : CellTableau Shape T, J.content t i • jmSpectralProjector J t ∧
    minpoly K (J.L i) = ∏ c ∈ contents J i, (Polynomial.X - Polynomial.C c) := g68n_spec J hsep i

end SeparatedDefinitions

end
