-- Prove2me | solution 2 for QCQPTightness.Exact.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T06:13:59.680281+00:00
-- url     : https://prove2.me/submissions/d8159902-7237-4c64-8cc2-7a97d828b7dd

import Mathlib
import Definitions.Def_QCQPTightness_Exact_QCQP
import Definitions.Def_QCQPTightness_Exact_Faces
import Definitions.Def_QCQPTightness_Exact_Proj
import Theorems.Thm_LP_farkas

-- carved verbatim out of submission 44f0948c-9e47-4ff2-abbf-de9fbef8a29d, lines 3117-3126

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def LP.DualFeas (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    Set ((ι → ℝ) × (κ → ℝ)) :=
  {yz | 0 ≤ yz.1 ∧ ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j = c}

def LP.Feas (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ) : Set E :=
  {x | (∀ i, a i x ≤ b i) ∧ ∀ j, e j x = d j}

end

noncomputable section
open Matrix

def argmaxOn {n : ℕ} (S : Set (Fin n → ℝ)) (u : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ S ∧ ∀ y ∈ S, u ⬝ᵥ y ≤ u ⬝ᵥ x}

theorem aux_mem_argmaxOn {n : ℕ} {S : Set (Fin n → ℝ)} {u x : Fin n → ℝ} :
    x ∈ argmaxOn S u ↔ x ∈ S ∧ ∀ y ∈ S, u ⬝ᵥ y ≤ u ⬝ᵥ x := Iff.rfl

def poly {n p : ℕ} (a : Fin p → Fin n → ℝ) (b : Fin p → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ j, a j ⬝ᵥ x ≤ b j}

theorem aux_mem_poly {n p : ℕ} {a : Fin p → Fin n → ℝ} {b : Fin p → ℝ} {x : Fin n → ℝ} :
    x ∈ poly a b ↔ ∀ j, a j ⬝ᵥ x ≤ b j := Iff.rfl

open Classical in
def tightSet {n p : ℕ} (a : Fin p → Fin n → ℝ) (b : Fin p → ℝ) (F : Set (Fin n → ℝ)) :
    Finset (Fin p) :=
  Finset.univ.filter fun j => ∀ x ∈ F, a j ⬝ᵥ x = b j

theorem aux_mem_tightSet {n p : ℕ} {a : Fin p → Fin n → ℝ} {b : Fin p → ℝ}
    {F : Set (Fin n → ℝ)} {j : Fin p} :
    j ∈ tightSet a b F ↔ ∀ x ∈ F, a j ⬝ᵥ x = b j := by
  classical
  simp [tightSet]

theorem aux_small {ι : Type*} [Finite ι] (g h : ι → ℝ) (P : ι → Prop)
    (hg : ∀ i, P i → g i < 0) : ∃ ε > 0, ∀ i, P i → g i + ε * h i < 0 := by
  have key : ∀ i, ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), P i → g i + ε * h i < 0 := by
    intro i
    by_cases hp : P i
    · have ht : Filter.Tendsto (fun ε : ℝ => g i + ε * h i) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (g i)) := by
        have hc : Continuous (fun ε : ℝ => g i + ε * h i) := by fun_prop
        have := hc.tendsto 0
        simp only [zero_mul, add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact (ht.eventually (gt_mem_nhds (hg i hp))).mono fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => absurd h hp
  obtain ⟨ε, h1, h2⟩ := ((Filter.eventually_all.2 key).and
    (self_mem_nhdsWithin : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0), x ∈ Set.Ioi 0)).exists
  exact ⟨ε, h2, fun i hi => h1 i hi⟩

theorem convex_argmaxOn {n : ℕ} {S : Set (Fin n → ℝ)} (hS : Convex ℝ S) (u : Fin n → ℝ) :
    Convex ℝ (argmaxOn S u) := by
  intro x hx y hy s t hs ht hst
  rw [aux_mem_argmaxOn] at hx hy ⊢
  refine ⟨hS hx.1 hy.1 hs ht hst, fun z hz => ?_⟩
  have h1 := hx.2 z hz
  have e : u ⬝ᵥ y = u ⬝ᵥ x := le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, e,
    ← add_mul, hst, one_mul]
  exact h1

theorem convex_poly {n p : ℕ} (a : Fin p → Fin n → ℝ) (b : Fin p → ℝ) :
    Convex ℝ (poly a b) := by
  intro x hx y hy s t hs ht hst
  rw [aux_mem_poly] at hx hy ⊢
  intro j
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  calc s * (a j ⬝ᵥ x) + t * (a j ⬝ᵥ y) ≤ s * b j + t * b j :=
        add_le_add (mul_le_mul_of_nonneg_left (hx j) hs) (mul_le_mul_of_nonneg_left (hy j) ht)
    _ = b j := by rw [← add_mul, hst, one_mul]

theorem exists_mem_argmaxOn_slack {n p : ℕ} (a : Fin p → Fin n → ℝ) (b : Fin p → ℝ)
    (u : Fin n → ℝ) (hne : (argmaxOn (poly a b) u).Nonempty) :
    ∃ x₀ ∈ argmaxOn (poly a b) u,
      ∀ j, j ∉ tightSet a b (argmaxOn (poly a b) u) → a j ⬝ᵥ x₀ < b j := by
  classical
  obtain ⟨xs, hxs⟩ := hne
  have hz : ∀ j, ∃ z ∈ argmaxOn (poly a b) u,
      (j ∉ tightSet a b (argmaxOn (poly a b) u) → a j ⬝ᵥ z < b j) := by
    intro j
    by_cases hj : j ∈ tightSet a b (argmaxOn (poly a b) u)
    · exact ⟨xs, hxs, fun h => absurd hj h⟩
    · have hj' := hj
      rw [aux_mem_tightSet] at hj'
      push Not at hj'
      obtain ⟨z, hzF, hzne⟩ := hj'
      exact ⟨z, hzF, fun _ => lt_of_le_of_ne ((aux_mem_poly.1 hzF.1) j) hzne⟩
  choose z hzF hzlt using hz
  obtain ⟨Z, hZF, hZlt⟩ : ∃ Z : Option (Fin p) → Fin n → ℝ,
      (∀ o, Z o ∈ argmaxOn (poly a b) u) ∧
      ∀ j, j ∉ tightSet a b (argmaxOn (poly a b) u) → a j ⬝ᵥ Z (some j) < b j :=
    ⟨fun o => o.elim xs z, fun o => by cases o with
      | none => exact hxs
      | some j => exact hzF j, fun j hj => hzlt j hj⟩
  obtain ⟨c, hc, hsum⟩ : ∃ c : ℝ, 0 < c ∧ ∑ _o : Option (Fin p), c = 1 := by
    refine ⟨1 / (p + 1), by positivity, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_option, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  refine ⟨∑ o, c • Z o, (convex_argmaxOn (convex_poly a b) u).sum_mem (fun _ _ => hc.le) hsum
    (fun o _ => hZF o), fun j hj => ?_⟩
  rw [dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul]
  calc ∑ o, c * (a j ⬝ᵥ Z o) < ∑ _o : Option (Fin p), c * b j :=
        Finset.sum_lt_sum (fun o _ => mul_le_mul_of_nonneg_left
          ((aux_mem_poly.1 (hZF o).1) j) hc.le)
          ⟨some j, Finset.mem_univ _, mul_lt_mul_of_pos_left (hZlt j hj) hc⟩
    _ = b j := by rw [← Finset.sum_mul, hsum, one_mul]

theorem argmaxOn_eq_tight {n p : ℕ} (a : Fin p → Fin n → ℝ) (b : Fin p → ℝ)
    (u : Fin n → ℝ) (hne : (argmaxOn (poly a b) u).Nonempty) :
    argmaxOn (poly a b) u =
      {x | x ∈ poly a b ∧ ∀ j ∈ tightSet a b (argmaxOn (poly a b) u), a j ⬝ᵥ x = b j} := by
  ext y
  constructor
  · intro hy
    exact ⟨hy.1, fun j hj => (aux_mem_tightSet.1 hj) y hy⟩
  · rintro ⟨hyP, hyT⟩
    obtain ⟨x0, hx0, hx0lt⟩ := exists_mem_argmaxOn_slack a b u hne
    obtain ⟨ε, hε, hεlt⟩ := aux_small (fun j => a j ⬝ᵥ x0 - b j)
      (fun j => a j ⬝ᵥ x0 - a j ⬝ᵥ y)
      (fun j => j ∉ tightSet a b (argmaxOn (poly a b) u))
      (fun j hj => by have := hx0lt j hj; linarith)
    have hzP : x0 + ε • (x0 - y) ∈ poly a b := by
      rw [aux_mem_poly]
      intro j
      rw [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]
      by_cases hj : j ∈ tightSet a b (argmaxOn (poly a b) u)
      · rw [(aux_mem_tightSet.1 hj) x0 hx0, hyT j hj]
        simp
      · have := hεlt j hj
        linarith
    rw [aux_mem_argmaxOn] at hx0 ⊢
    refine ⟨hyP, fun y' hy' => ?_⟩
    have h1 := hx0.2 y' hy'
    have h2 := hx0.2 _ hzP
    rw [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul] at h2
    have : u ⬝ᵥ x0 ≤ u ⬝ᵥ y := by
      by_contra hlt
      push Not at hlt
      have := mul_pos hε (sub_pos.2 hlt)
      linarith
    linarith

end

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def aux1_dotL {n : Type*} [Fintype n] (u : n → ℝ) : Module.Dual ℝ (n → ℝ) where
  toFun v := u ⬝ᵥ v
  map_add' v w := dotProduct_add u v w
  map_smul' t v := by simp [dotProduct_smul]

lemma aux1_dotL_apply {n : Type*} [Fintype n] (u v : n → ℝ) : aux1_dotL u v = u ⬝ᵥ v := rfl

lemma aux1_dotL_inj {n : Type*} [Fintype n] {u w : n → ℝ} (h : aux1_dotL u = aux1_dotL w) :
    u = w := by
  classical
  funext j
  have := congrArg (fun φ : Module.Dual ℝ (n → ℝ) => φ (Pi.single j 1)) h
  simpa [aux1_dotL_apply, dotProduct_single] using this

end

noncomputable section
open Matrix

theorem aux_dotL_add {n : ℕ} (u w : Fin n → ℝ) :
    aux1_dotL (u + w) = aux1_dotL u + aux1_dotL w := by
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.add_apply, aux1_dotL_apply, add_dotProduct]

theorem aux_sum_smul_dot {n : ℕ} {ι : Type*} [Fintype ι] (y : ι → ℝ) (a : ι → Fin n → ℝ)
    (x : Fin n → ℝ) : (∑ j, y j • a j) ⬝ᵥ x = ∑ j, y j * (a j ⬝ᵥ x) := by
  simp [sum_dotProduct, smul_dotProduct]

theorem aux_dotL_sum {n : ℕ} {ι : Type*} [Fintype ι] (c : ι → ℝ) (A : ι → Fin n → ℝ) :
    aux1_dotL (∑ i, c i • A i) = ∑ i, c i • aux1_dotL (A i) := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.sum_apply, aux1_dotL_apply, aux_sum_smul_dot]
  simp only [LinearMap.smul_apply, aux1_dotL_apply, smul_eq_mul]

end

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma aux1_alt (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty) (t : ℝ)
    (h : ∀ x ∈ LP.Feas a b e d, c x < t) :
    ∃ yz ∈ LP.DualFeas a e c, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d < t := by
  classical
  let a' : Option ι → Module.Dual ℝ E := fun o => o.elim (-c) a
  let b' : Option ι → ℝ := fun o => o.elim (-t) b
  have hinf : ¬ ∃ x : E, (∀ i, a' i x ≤ b' i) ∧ ∀ j, e j x = d j := by
    rintro ⟨x, hx1, hx2⟩
    have h1 := h x ⟨fun i => hx1 (some i), hx2⟩
    have h2 := hx1 none
    simp only [a', b', Option.elim, LinearMap.neg_apply] at h2
    linarith
  obtain ⟨y', z, hy', hsum, hneg⟩ := (LP.farkas a' b' e d).1 hinf
  rw [Fintype.sum_option] at hsum
  simp only [dotProduct, Fintype.sum_option] at hneg
  simp only [a', b', Option.elim, smul_neg] at hsum hneg
  have hy0 : 0 ≤ y' none := hy' none
  rcases hy0.eq_or_lt with h0 | h0
  · exfalso
    obtain ⟨x0, hx0⟩ := hP
    refine (LP.farkas a b e d).2 ⟨fun i => y' (some i), z, fun i => hy' (some i), ?_, ?_⟩
      ⟨x0, hx0⟩
    · rw [← h0] at hsum; simpa using hsum
    · simp only [dotProduct]; rw [← h0] at hneg; simpa using hneg
  · refine ⟨(fun i => y' (some i) / y' none, fun j => z j / y' none),
      ⟨fun i => div_nonneg (hy' _) h0.le, ?_⟩, ?_⟩
    · have hAB : ∑ i, y' (some i) • a i + ∑ j, z j • e j = y' none • c := by
        rw [← sub_eq_zero, ← hsum]; abel
      show ∑ i, (y' (some i) / y' none) • a i + ∑ j, (z j / y' none) • e j = c
      have hr : ∀ (r : ℝ) (φ : Module.Dual ℝ E), (r / y' none) • φ = (y' none)⁻¹ • (r • φ) :=
        fun r φ => by rw [smul_smul, div_eq_inv_mul]
      simp only [hr]
      rw [← Finset.smul_sum, ← Finset.smul_sum, ← smul_add, hAB, smul_smul,
        inv_mul_cancel₀ h0.ne', one_smul]
    · simp only [dotProduct]
      have : ∑ i, y' (some i) / y' none * b i + ∑ j, z j / y' none * d j =
          (∑ i, y' (some i) * b i + ∑ j, z j * d j) / y' none := by
        rw [add_div, Finset.sum_div, Finset.sum_div]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this, div_lt_iff₀ h0]
      linarith

theorem LP.dualFeas_nonempty_of_bddAbove
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty)
    (hb : BddAbove (c '' LP.Feas a b e d)) : (LP.DualFeas a e c).Nonempty := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨yz, hyz, -⟩ := aux1_alt a b e d c hP (M + 1) fun x hx => by
    have := hM ⟨x, hx, rfl⟩
    linarith
  exact ⟨yz, hyz⟩

theorem LP.weak_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) {x : E} (hx : x ∈ LP.Feas a b e d)
    {yz : (ι → ℝ) × (κ → ℝ)} (hyz : yz ∈ LP.DualFeas a e c) :
    c x ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d := by
  obtain ⟨hax, hex⟩ := hx
  obtain ⟨hy, hsum⟩ := hyz
  have h := congrArg (fun φ : Module.Dual ℝ E => φ x) hsum
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    hex] at h
  have hle : ∑ i, yz.1 i * a i x ≤ ∑ i, yz.1 i * b i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hax i) (hy i)
  simp only [dotProduct]
  linarith

lemma aux1_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty)
    (hb : BddAbove (c '' LP.Feas a b e d)) :
    ∃ x ∈ LP.Feas a b e d, ∀ x' ∈ LP.Feas a b e d, c x' ≤ c x := by
  by_contra hno
  push Not at hno
  have hlt : ∀ x ∈ LP.Feas a b e d, c x < sSup (c '' LP.Feas a b e d) := fun x hx => by
    obtain ⟨x', hx', hlt⟩ := hno x hx
    exact lt_of_lt_of_le hlt (le_csSup hb ⟨x', hx', rfl⟩)
  obtain ⟨yz, hyz, hobj⟩ := aux1_alt a b e d c hP _ hlt
  have : sSup (c '' LP.Feas a b e d) ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d :=
    csSup_le (hP.image c) (by rintro _ ⟨x, hx, rfl⟩; exact LP.weak_duality a b e d c hx hyz)
  linarith

def aux1_T (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) :
    (ι → ℝ) × (κ → ℝ) →ₗ[ℝ] Module.Dual ℝ E where
  toFun yz := ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
      ← Finset.smul_sum, smul_add, RingHom.id_apply]

lemma aux1_dualFeas_eq (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    LP.DualFeas a e c =
      LP.Feas (fun i => -(LinearMap.proj i ∘ₗ LinearMap.fst ℝ (ι → ℝ) (κ → ℝ))) 0
        (fun k => Module.Dual.eval ℝ E (Module.finBasis ℝ E k) ∘ₗ aux1_T a e)
        (fun k => c (Module.finBasis ℝ E k)) := by
  ext yz
  simp only [LP.DualFeas, LP.Feas, Set.mem_setOf_eq, LinearMap.neg_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_fst, LinearMap.coe_proj, Function.eval, Pi.zero_apply,
    neg_nonpos, Module.Dual.eval_apply]
  constructor
  · rintro ⟨hy, hsum⟩
    exact ⟨fun i => hy i, fun k => by rw [← hsum]; rfl⟩
  · rintro ⟨hy, hk⟩
    refine ⟨fun i => hy i, ?_⟩
    have : aux1_T a e yz = c := (Module.finBasis ℝ E).ext fun k => hk k
    exact this

def aux1_obj (b : ι → ℝ) (d : κ → ℝ) : Module.Dual ℝ ((ι → ℝ) × (κ → ℝ)) where
  toFun yz := yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct]; ring
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, RingHom.id_apply]; ring

lemma aux1_dual_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E)
    (d : κ → ℝ) (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ yz ∈ LP.DualFeas a e c, ∀ yz' ∈ LP.DualFeas a e c,
      yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ yz'.1 ⬝ᵥ b + yz'.2 ⬝ᵥ d := by
  obtain ⟨x0, hx0⟩ := hP
  rw [aux1_dualFeas_eq] at hD ⊢
  obtain ⟨yz, hyz, hmax⟩ := aux1_attain _ _ _ _ (-aux1_obj b d) hD (by
    refine ⟨-c x0, ?_⟩
    rintro _ ⟨yz', hyz', rfl⟩
    rw [← aux1_dualFeas_eq] at hyz'
    have := LP.weak_duality a b e d c hx0 hyz'
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    exact this)
  refine ⟨yz, hyz, fun yz' hyz' => ?_⟩
  have := hmax yz' hyz'
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
  exact this

theorem LP.strong_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ v : ℝ, IsGreatest (c '' LP.Feas a b e d) v ∧
      IsLeast ((fun yz => yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d) '' LP.DualFeas a e c) v := by
  obtain ⟨yz, hyz, hmin⟩ := aux1_dual_attain a b e d c hP hD
  obtain ⟨x, hx, hxw⟩ : ∃ x ∈ LP.Feas a b e d, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ c x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨yz', hyz', hlt⟩ := aux1_alt a b e d c hP _ hcon
    linarith [hmin yz' hyz']
  refine ⟨yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d,
    ⟨⟨x, hx, le_antisymm (LP.weak_duality a b e d c hx hyz) hxw⟩, ?_⟩,
    ⟨⟨yz, hyz, rfl⟩, ?_⟩⟩
  · rintro _ ⟨x', hx', rfl⟩; exact LP.weak_duality a b e d c hx' hyz
  · rintro _ ⟨yz', hyz', rfl⟩; exact hmin yz' hyz'

end

noncomputable section
open Matrix

theorem aux_lpv {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Fin n → ℝ) (b : ι → ℝ) (E : κ → Fin n → ℝ) (d : κ → ℝ) (w : Fin n → ℝ)
    (hne : ∃ x, (∀ i, A i ⬝ᵥ x ≤ b i) ∧ ∀ k, E k ⬝ᵥ x = d k)
    (hbdd : ∃ M, ∀ x, (∀ i, A i ⬝ᵥ x ≤ b i) → (∀ k, E k ⬝ᵥ x = d k) → w ⬝ᵥ x ≤ M) :
    ∃ x, ((∀ i, A i ⬝ᵥ x ≤ b i) ∧ ∀ k, E k ⬝ᵥ x = d k) ∧
      (∀ x', (∀ i, A i ⬝ᵥ x' ≤ b i) → (∀ k, E k ⬝ᵥ x' = d k) → w ⬝ᵥ x' ≤ w ⬝ᵥ x) ∧
      ∃ (y : ι → ℝ) (z : κ → ℝ), (∀ i, 0 ≤ y i) ∧
        ∑ i, y i • A i + ∑ k, z k • E k = w ∧
        ∑ i, y i * b i + ∑ k, z k * d k = w ⬝ᵥ x := by
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨M, hM⟩ := hbdd
  have hP : (LP.Feas (fun i => aux1_dotL (A i)) b (fun k => aux1_dotL (E k)) d).Nonempty :=
    ⟨x0, hx0⟩
  have hD := LP.dualFeas_nonempty_of_bddAbove _ b _ d (aux1_dotL w) hP
    ⟨M, by rintro _ ⟨x, hx, rfl⟩; exact hM x hx.1 hx.2⟩
  obtain ⟨v, ⟨⟨x, hx, hxv⟩, hub⟩, ⟨⟨yz, hyz, hyzv⟩, -⟩⟩ :=
    LP.strong_duality _ b _ d (aux1_dotL w) hP hD
  refine ⟨x, hx, fun x' h1 h2 => ?_, yz.1, yz.2, fun i => hyz.1 i, ?_, ?_⟩
  · have := hub ⟨x', ⟨h1, h2⟩, rfl⟩
    rw [← hxv] at this
    exact this
  · have h : ∑ i, yz.1 i • aux1_dotL (A i) + ∑ k, yz.2 k • aux1_dotL (E k) = aux1_dotL w :=
      hyz.2
    rw [← aux_dotL_sum, ← aux_dotL_sum, ← aux_dotL_add] at h
    exact aux1_dotL_inj h
  · rw [← aux1_dotL_apply, hxv, ← hyzv]
    rfl

theorem argmaxOn_nonempty {n p : ℕ} (a : Fin p → Fin n → ℝ) (b : Fin p → ℝ) (u : Fin n → ℝ)
    (hne : (poly a b).Nonempty) (hbdd : BddAbove ((fun x => u ⬝ᵥ x) '' poly a b)) :
    (argmaxOn (poly a b) u).Nonempty := by
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨x, hx, hmax, -⟩ := aux_lpv a b (fun k : Empty => k.elim) (fun k => k.elim) u
    ⟨x0, hx0, fun k => k.elim⟩ ⟨M, fun x hx _ => hM ⟨x, hx, rfl⟩⟩
  exact ⟨x, hx.1, fun y hy => hmax y hy fun k => k.elim⟩

theorem aux_expand {p r : ℕ} (y bb s : Fin p → ℝ) (t : Fin r → ℝ) (L : Fin r → Fin p → ℝ) :
    ∑ j, (bb j - s j) * (y j + ∑ k, t k * L k j) =
      (∑ j, y j * bb j - ∑ j, y j * s j) +
        (∑ k, t k * ∑ j, L k j * bb j - ∑ k, t k * ∑ j, L k j * s j) := by
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by ring
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_face_certificate {n p : ℕ} (a : Fin p → Fin n → ℝ) (b : Fin p → ℝ)
    (u : Fin n → ℝ) (hne : (argmaxOn (poly a b) u).Nonempty) (w : Fin n → ℝ) (c : ℝ)
    (hw : ∀ x ∈ argmaxOn (poly a b) u, w ⬝ᵥ x ≤ c) :
    ∃ l μ : Fin p → ℝ, (∀ j, 0 ≤ l j) ∧
      (∀ j, j ∉ tightSet a b (argmaxOn (poly a b) u) → μ j = 0) ∧
      ∑ j, (l j + μ j) • a j = w ∧ ∑ j, (l j + μ j) * b j ≤ c := by
  classical
  have hF := argmaxOn_eq_tight a b u hne
  obtain ⟨x0, hx0⟩ := hne
  generalize hT : tightSet a b (argmaxOn (poly a b) u) = T at hF ⊢
  have hfe : ∀ x, ((∀ i, a i ⬝ᵥ x ≤ b i) ∧
      ∀ k, (if k ∈ T then a k else 0) ⬝ᵥ x = (if k ∈ T then b k else 0)) ↔
      x ∈ argmaxOn (poly a b) u := by
    intro x
    rw [hF]
    simp only [Set.mem_setOf_eq, aux_mem_poly]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun j hj => ?_⟩
      have := h2 j
      simp only [if_pos hj] at this
      exact this
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun k => ?_⟩
      split_ifs with hk
      · exact h2 k hk
      · simp
  obtain ⟨xo, hxo, -, l, z, hl, hs, hb⟩ :=
    aux_lpv a b (fun k => if k ∈ T then a k else 0) (fun k => if k ∈ T then b k else 0) w
      ⟨x0, (hfe x0).2 hx0⟩ ⟨c, fun x h1 h2 => hw x ((hfe x).1 ⟨h1, h2⟩)⟩
  refine ⟨l, fun j => if j ∈ T then z j else 0, hl, fun j hj => if_neg hj, ?_, ?_⟩
  · rw [← hs]
    simp only [add_smul, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · have : ∑ j, (l j + (if j ∈ T then z j else 0)) * b j = w ⬝ᵥ xo := by
      rw [← hb]
      simp only [add_mul, Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [this]
    exact hw xo ((hfe xo).1 hxo)

theorem aux_support {n p : ℕ} (a : Fin p → Fin n → ℝ) (b : Fin p → ℝ) (u : Fin n → ℝ)
    (x0 : Fin n → ℝ) (hx0 : x0 ∈ argmaxOn (poly a b) u) (Y : Fin p → ℝ) (ζ : ℝ)
    (hY : ∀ k, 0 ≤ Y k) (h1 : ∑ k, Y k • a k = ζ • u)
    (h2 : ∑ k, Y k * b k = ζ * (u ⬝ᵥ x0)) :
    ∀ k, k ∉ tightSet a b (argmaxOn (poly a b) u) → Y k = 0 := by
  intro k hk
  rw [aux_mem_tightSet] at hk
  push Not at hk
  obtain ⟨x, hx, hxk⟩ := hk
  rw [aux_mem_argmaxOn] at hx hx0
  have hxP := aux_mem_poly.1 hx.1
  have hux : u ⬝ᵥ x = u ⬝ᵥ x0 := le_antisymm (hx0.2 x hx.1) (hx.2 x0 hx0.1)
  have hdot : ∑ i, Y i * (a i ⬝ᵥ x) = ζ * (u ⬝ᵥ x) := by
    rw [← aux_sum_smul_dot, h1, smul_dotProduct, smul_eq_mul]
  have hsum : ∑ i, Y i * (b i - a i ⬝ᵥ x) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, h2, hdot, hux, sub_self]
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ Y i * (b i - a i ⬝ᵥ x) :=
    fun i _ => mul_nonneg (hY i) (sub_nonneg.2 (hxP i))
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum k (Finset.mem_univ _)
  have hpos : 0 < b k - a k ⬝ᵥ x := sub_pos.2 (lt_of_le_of_ne (hxP k) hxk)
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · linarith

theorem exists_strict_dual {n p : ℕ} (a : Fin p → Fin n → ℝ) (b : Fin p → ℝ)
    (u : Fin n → ℝ) (hne : (argmaxOn (poly a b) u).Nonempty) :
    ∃ y : Fin p → ℝ,
      (∀ j ∈ tightSet a b (argmaxOn (poly a b) u), 0 < y j) ∧
      (∀ j, j ∉ tightSet a b (argmaxOn (poly a b) u) → y j = 0) ∧
      ∑ j, y j • a j = u := by
  classical
  obtain ⟨x0, hx0⟩ := hne
  have hx0P : ∀ j, a j ⬝ᵥ x0 ≤ b j := aux_mem_poly.1 hx0.1
  have hx0max : ∀ y ∈ poly a b, u ⬝ᵥ y ≤ u ⬝ᵥ x0 := hx0.2
  obtain ⟨xb, ⟨hxbP, -⟩, hxbmax, y0, z0, hy0, hy0s, hy0b⟩ :=
    aux_lpv a b (fun k : Empty => k.elim) (fun k => k.elim) u ⟨x0, hx0P, fun k => k.elim⟩
      ⟨u ⬝ᵥ x0, fun x hx _ => hx0max x hx⟩
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hy0s hy0b
  have hub : u ⬝ᵥ xb = u ⬝ᵥ x0 :=
    le_antisymm (hx0max xb hxbP) (hxbmax x0 hx0P (fun k => k.elim))
  have hj : ∀ j, ∃ (Y : Fin p → ℝ) (ζ : ℝ), (∀ k, 0 ≤ Y k) ∧ 0 ≤ ζ ∧
      ∑ k, Y k • a k = ζ • u ∧ ∑ k, Y k * b k = ζ * (u ⬝ᵥ x0) ∧
      (j ∈ tightSet a b (argmaxOn (poly a b) u) → 1 ≤ Y j) := by
    intro j
    by_cases hjT : j ∈ tightSet a b (argmaxOn (poly a b) u)
    · have hjF := aux_mem_tightSet.1 hjT
      let A : Option (Fin p) → Fin n → ℝ := fun o => o.elim (-u) a
      let bb : Option (Fin p) → ℝ := fun o => o.elim (-(u ⬝ᵥ x0)) b
      have hfeasF : ∀ x, (∀ o, A o ⬝ᵥ x ≤ bb o) → x ∈ argmaxOn (poly a b) u := by
        intro x hx
        have hxP : x ∈ poly a b := fun k => hx (some k)
        have hxu : u ⬝ᵥ x0 ≤ u ⬝ᵥ x := by
          have := hx none
          simp only [A, bb, Option.elim, neg_dotProduct] at this
          linarith
        exact ⟨hxP, fun y hy => (hx0max y hy).trans hxu⟩
      have hfeas0 : ∀ o, A o ⬝ᵥ x0 ≤ bb o := by
        intro o
        cases o with
        | none => simp [A, bb]
        | some k => exact hx0P k
      have hbdd : ∀ x, (∀ o, A o ⬝ᵥ x ≤ bb o) → (∀ k : Empty, k.elim ⬝ᵥ x = (k.elim : ℝ)) →
          (-a j) ⬝ᵥ x ≤ -b j := by
        intro x hx _
        rw [neg_dotProduct, hjF x (hfeasF x hx)]
      obtain ⟨xo, ⟨hxoA, -⟩, -, y, z, hy, hys, hyb⟩ :=
        aux_lpv A bb (fun k : Empty => k.elim) (fun k => k.elim) (-a j)
          ⟨x0, hfeas0, fun k => k.elim⟩ ⟨-b j, hbdd⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fintype.sum_option, A, bb,
        Option.elim] at hys hyb
      have hxo := hjF xo (hfeasF xo hxoA)
      rw [neg_dotProduct, hxo] at hyb
      have e : ∑ k, y (some k) • a k = y none • u - a j := by
        rw [eq_sub_of_add_eq' hys, smul_neg, sub_neg_eq_add, neg_add_eq_sub]
      refine ⟨fun k => y (some k) + if k = j then 1 else 0, y none, fun k => ?_, hy none, ?_, ?_,
        fun _ => ?_⟩
      · exact add_nonneg (hy _) (by split_ifs <;> norm_num)
      · simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, e, sub_add_cancel]
      · simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        linarith
      · show 1 ≤ y (some j) + if j = j then 1 else 0
        rw [if_pos rfl]
        linarith [hy (some j)]
    · exact ⟨0, 0, fun _ => le_rfl, le_rfl, by simp, by simp, fun h => absurd h hjT⟩
  choose Y ζ hY hζ hYa hYb hYj using hj
  have hZt : 0 < 1 + ∑ j, ζ j := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ => hζ j)
  have ha2 : ∑ k, ∑ j, Y j k • a k = ∑ j, ζ j • u := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hYa j
  have hb2 : ∑ k, ∑ j, Y j k * b k = ∑ j, ζ j * (u ⬝ᵥ x0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hYb j
  have hYta : ∑ k, (y0 k + ∑ j, Y j k) • a k = (1 + ∑ j, ζ j) • u := by
    simp only [add_smul, Finset.sum_add_distrib, Finset.sum_smul, one_smul, ha2, hy0s]
  have hYtb : ∑ k, (y0 k + ∑ j, Y j k) * b k = (1 + ∑ j, ζ j) * (u ⬝ᵥ x0) := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, one_mul, hb2, hy0b, hub]
  have hYt0 : ∀ k, 0 ≤ y0 k + ∑ j, Y j k :=
    fun k => add_nonneg (hy0 k) (Finset.sum_nonneg fun j _ => hY j k)
  have hsupp := aux_support a b u x0 hx0 _ _ hYt0 hYta hYtb
  refine ⟨fun k => (1 + ∑ j, ζ j)⁻¹ * (y0 k + ∑ j, Y j k), fun j hj => ?_, fun j hj => ?_, ?_⟩
  · refine mul_pos (inv_pos.2 hZt) ?_
    have h1 := hYj j hj
    have h2 : Y j j ≤ ∑ j', Y j' j :=
      Finset.single_le_sum (f := fun j' => Y j' j) (fun j' _ => hY j' j) (Finset.mem_univ j)
    linarith [hy0 j]
  · simp only [hsupp j hj, mul_zero]
  · calc ∑ j, ((1 + ∑ j, ζ j)⁻¹ * (y0 j + ∑ j', Y j' j)) • a j
          = (1 + ∑ j, ζ j)⁻¹ • ∑ j, (y0 j + ∑ j', Y j' j) • a j := by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [mul_smul]
      _ = u := by rw [hYta, smul_smul, inv_mul_cancel₀ hZt.ne', one_smul]

theorem argmaxOn_perturb {n p r : ℕ} (a : Fin p → Fin n → ℝ) (b : Fin p → ℝ)
    (u : Fin n → ℝ) (hne : (argmaxOn (poly a b) u).Nonempty)
    (w : Fin r → Fin n → ℝ) (c : Fin r → ℝ)
    (hw : ∀ k, ∀ x ∈ argmaxOn (poly a b) u, w k ⬝ᵥ x ≤ c k) :
    ∃ δ > 0, ∀ t : Fin r → ℝ, (∀ k, 0 ≤ t k ∧ t k ≤ δ) →
      ∀ x₀ ∈ argmaxOn (poly a b) u, ∀ x ∈ poly a b,
        (u + ∑ k, t k • w k) ⬝ᵥ x ≤ u ⬝ᵥ x₀ + ∑ k, t k * c k := by
  classical
  obtain ⟨y, hyT, hyN, hyu⟩ := exists_strict_dual a b u hne
  have hcert : ∀ k, ∃ l μ : Fin p → ℝ, (∀ j, 0 ≤ l j) ∧
      (∀ j, j ∉ tightSet a b (argmaxOn (poly a b) u) → μ j = 0) ∧
      ∑ j, (l j + μ j) • a j = w k ∧ ∑ j, (l j + μ j) * b j ≤ c k :=
    fun k => exists_face_certificate a b u hne (w k) (c k) (hw k)
  choose l μ hl hμ hlw hlc using hcert
  obtain ⟨δ, hδ, hδlt⟩ := aux_small (fun j => -y j) (fun j => ∑ k, |μ k j|)
    (fun j => j ∈ tightSet a b (argmaxOn (poly a b) u))
    (fun j hj => by have := hyT j hj; linarith)
  refine ⟨δ, hδ, fun t ht x0 hx0 x hx => ?_⟩
  have hxP := aux_mem_poly.1 hx
  have key : ∀ j, 0 ≤ y j + ∑ k, t k * (l k j + μ k j) := by
    intro j
    by_cases hj : j ∈ tightSet a b (argmaxOn (poly a b) u)
    · have h1 : ∀ k, -(δ * |μ k j|) ≤ t k * (l k j + μ k j) := by
        intro k
        have h0 := neg_abs_le (μ k j)
        have h2 : t k * (-|μ k j|) ≤ t k * (l k j + μ k j) :=
          mul_le_mul_of_nonneg_left (by linarith [hl k j]) (ht k).1
        have h3 : t k * |μ k j| ≤ δ * |μ k j| :=
          mul_le_mul_of_nonneg_right (ht k).2 (abs_nonneg _)
        rw [mul_neg] at h2
        linarith
      have hs := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => h1 k
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at hs
      have := hδlt j hj
      linarith
    · have hz : ∀ k, μ k j = 0 := fun k => hμ k j hj
      rw [hyN j hj]
      simp only [hz, add_zero, zero_add]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (ht k).1 (hl k j)
  have hux : u ⬝ᵥ x = ∑ j, y j * (a j ⬝ᵥ x) := by rw [← hyu, aux_sum_smul_dot]
  have hux0 : u ⬝ᵥ x0 = ∑ j, y j * b j := by
    rw [← hyu, aux_sum_smul_dot]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ tightSet a b (argmaxOn (poly a b) u)
    · rw [aux_mem_tightSet.1 hj x0 hx0]
    · rw [hyN j hj, zero_mul, zero_mul]
  have hwx : ∀ k, w k ⬝ᵥ x = ∑ j, (l k j + μ k j) * (a j ⬝ᵥ x) :=
    fun k => by rw [← hlw k, aux_sum_smul_dot]
  have hlhs : (u + ∑ k, t k • w k) ⬝ᵥ x = u ⬝ᵥ x + ∑ k, t k * (w k ⬝ᵥ x) := by
    rw [add_dotProduct, sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
  have hc : ∑ k, t k * (∑ j, (l k j + μ k j) * b j) ≤ ∑ k, t k * c k :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hlc k) (ht k).1
  have hnn : 0 ≤ ∑ j, (b j - a j ⬝ᵥ x) * (y j + ∑ k, t k * (l k j + μ k j)) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (sub_nonneg.2 (hxP j)) (key j)
  have hexp : ∑ j, (b j - a j ⬝ᵥ x) * (y j + ∑ k, t k * (l k j + μ k j)) =
      (∑ j, y j * b j - ∑ j, y j * (a j ⬝ᵥ x)) +
        (∑ k, t k * ∑ j, (l k j + μ k j) * b j -
          ∑ k, t k * ∑ j, (l k j + μ k j) * (a j ⬝ᵥ x)) :=
    aux_expand y b (fun j => a j ⬝ᵥ x) t (fun k j => l k j + μ k j)
  rw [hlhs, hux, hux0]
  simp only [hwx]
  linarith

theorem argmaxOn_poly_isPoly {n p : ℕ} (a : Fin p → Fin n → ℝ) (b : Fin p → ℝ)
    (u : Fin n → ℝ) :
    ∃ (p' : ℕ) (a' : Fin p' → Fin n → ℝ) (b' : Fin p' → ℝ),
      argmaxOn (poly a b) u = poly a' b' := by
  by_cases hF : (argmaxOn (poly a b) u).Nonempty
  · obtain ⟨x0, hx0P, hx0⟩ := hF
    refine ⟨p + 1, Fin.cons (-u) a, Fin.cons (-(u ⬝ᵥ x0)) b, ?_⟩
    ext x
    simp only [aux_mem_argmaxOn, aux_mem_poly, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
      neg_dotProduct, neg_le_neg_iff]
    constructor
    · rintro ⟨hx, hmax⟩
      exact ⟨hmax x0 hx0P, hx⟩
    · rintro ⟨h0, hx⟩
      exact ⟨hx, fun y hy => (hx0 y hy).trans h0⟩
  · refine ⟨1, fun _ => 0, fun _ => -1, ?_⟩
    rw [Set.not_nonempty_iff_eq_empty.1 hF]
    ext x
    simp only [Set.mem_empty_iff_false, false_iff, aux_mem_poly, zero_dotProduct, not_forall,
      not_le]
    exact ⟨0, by norm_num⟩

end

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private lemma aux2_dot_self_nonneg {n : Type*} [Fintype n] (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

private lemma aux2_dot_self_pos {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (aux2_dot_self_nonneg v) (Ne.symm (mt dotProduct_self_eq_zero.1 hv))

private lemma aux2_interior_nonempty {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [T2Space W] [FiniteDimensional ℝ W]
    {s : Set W} (hs : Convex ℝ s) (h : affineSpan ℝ s = ⊤) : (interior s).Nonempty := by
  let e : W ≃L[ℝ] (Fin (Module.finrank ℝ W) → ℝ) :=
    (Module.finBasis ℝ W).equivFun.toContinuousLinearEquiv
  have h1 : Convex ℝ (e '' s) := hs.is_linear_image (f := ⇑e) e.toLinearMap.isLinear
  have h2 : affineSpan ℝ (e '' s) = ⊤ :=
    (AffineEquiv.span_eq_top_iff e.toLinearEquiv.toAffineEquiv).1 h
  obtain ⟨z, hz⟩ := (h1.interior_nonempty_iff_affineSpan_eq_top).2 h2
  have h3 : z ∈ e.toHomeomorph '' interior s := by
    rw [e.toHomeomorph.image_interior s]; exact hz
  obtain ⟨w, hw, -⟩ := h3
  exact ⟨w, hw⟩

private lemma aux2_isHermitian {n : Type*} {A : Matrix n n ℝ} (hA : A.IsSymm) : A.IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact hA

private lemma aux2_lim (a c μ : ℝ) (hμ : 0 < μ) (h : ∀ s : ℝ, s < c → a + s * μ ≤ 0) :
    a + c * μ ≤ 0 := by
  by_contra hc
  push Not at hc
  have hs : c - (a + c * μ) / (2 * μ) < c := by
    have : 0 < (a + c * μ) / (2 * μ) := by positivity
    linarith
  have := h _ hs
  have e : (c - (a + c * μ) / (2 * μ)) * μ = c * μ - (a + c * μ) / 2 := by field_simp
  rw [e] at this
  linarith

private lemma aux2_lin_nonneg (a b : ℝ) (h : ∀ t : ℝ, 0 ≤ t → b - t * a ≤ 0) : 0 ≤ a := by
  by_contra ha
  push Not at ha
  have ht : 0 ≤ (|b| + 1) / (-a) := div_nonneg (by positivity) (by linarith)
  have := h _ ht
  have e : (|b| + 1) / (-a) * a = -(|b| + 1) := by
    rw [div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self ha.ne, mul_one]
  rw [e] at this
  linarith [neg_abs_le b]

def psdForm (n : Type*) [Fintype n] : PointedCone ℝ (Matrix n n ℝ) where
  carrier := {A | ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ A *ᵥ v}
  add_mem' := by
    intro A B hA hB v
    simp only [Set.mem_ofPred_eq, Matrix.add_mulVec, dotProduct_add] at *
    exact add_nonneg (hA v) (hB v)
  zero_mem' := by intro v; simp
  smul_mem' := by
    intro t A hA v
    have h : (0 : ℝ) ≤ (t : ℝ) * (v ⬝ᵥ A *ᵥ v) := mul_nonneg t.2 (hA v)
    simp only [Matrix.smul_mulVec, dotProduct_smul]
    exact h

private lemma aux2_mem_psdForm {n : Type*} [Fintype n] {A : Matrix n n ℝ} :
    A ∈ psdForm n ↔ ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ A *ᵥ v := Iff.rfl

private lemma aux2_normalize {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ (c • v) ⬝ᵥ (c • v) = 1 := by
  have hpos := aux2_dot_self_pos hv
  have hs : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.2 hpos
  have hs2 : Real.sqrt (v ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hpos.le
  refine ⟨(Real.sqrt (v ⬝ᵥ v))⁻¹, inv_pos.2 hs, ?_⟩
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  linarith [hs2]

private lemma aux2_qf_smul {n : Type*} [Fintype n] (A : Matrix n n ℝ) (c : ℝ) (v : n → ℝ) :
    (c • v) ⬝ᵥ A *ᵥ (c • v) = c ^ 2 * (v ⬝ᵥ A *ᵥ v) := by
  simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

private def aux2_sph (n : Type*) [Fintype n] : Set (n → ℝ) := {v | v ⬝ᵥ v = 1}

private lemma aux2_sph_compact (n : Type*) [Fintype n] : IsCompact (aux2_sph n) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun v hv => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : v i * v i ≤ v ⬝ᵥ v :=
      Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
        (Finset.mem_univ i)
    have h2 : v ⬝ᵥ v = 1 := hv
    rw [Real.norm_eq_abs]
    nlinarith [abs_mul_abs_self (v i), abs_nonneg (v i)]

private lemma aux2_sph_ne {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ∈ aux2_sph n) : v ≠ 0 := by
  rintro rfl; simp [aux2_sph] at hv

open scoped MatrixOrder in
private lemma aux2_trace_mul_nonneg {n : Type*} [Fintype n] {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  have hB0 : 0 ≤ B := hB.nonneg
  have hS : (CFC.sqrt B).PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have hSS : CFC.sqrt B * CFC.sqrt B = B := CFC.sqrt_mul_sqrt_self B hB0
  have hSh : (CFC.sqrt B)ᴴ = CFC.sqrt B := hS.isHermitian.eq
  have h := (hA.mul_mul_conjTranspose_same (CFC.sqrt B)).trace_nonneg
  rw [hSh] at h
  rw [← hSS, ← mul_assoc, trace_mul_cycle]
  exact h

private lemma aux2_trace_vecMulVec {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    (M * vecMulVec x x).trace = x ⬝ᵥ M *ᵥ x := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma aux2_vecMulVec_mem {n : Type*} [Fintype n] (v : n → ℝ) : vecMulVec v v ∈ psdForm n := by
  intro w
  simpa using (posSemidef_vecMulVec_self_star v).dotProduct_mulVec_nonneg w

end

section
open Matrix

namespace RankRedKit

theorem aux_coercive_num {l a t d β c M g w : ℝ} (hl : 0 < l) (ha : l * a ≤ g) (ht : l * t ≤ w)
    (h0 : 0 ≤ l ^ 2 * a + 4 * l * d + 4 * β) (hF : g + 2 * d + c + w ≤ M) (ht0 : 0 ≤ t)
    (ha0 : 0 ≤ a) :
    a ≤ (2 * l * M + 4 * β - 2 * l * c) / l ^ 2 ∧ t ≤ (2 * l * M + 4 * β - 2 * l * c) / l ^ 2 := by
  have key : l ^ 2 * a + 2 * l ^ 2 * t ≤ 2 * l * M + 4 * β - 2 * l * c := by nlinarith
  have hl2 : 0 < l ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ hl2]; nlinarith
  · rw [le_div_iff₀ hl2]; nlinarith

end RankRedKit

namespace RankRedKit

def liftY {N : ℕ} (x : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) ℝ :=
  Matrix.fromBlocks (fun _ _ => 1) (fun _ j => x j) (fun i _ => x i) X

end RankRedKit

namespace RankRedKit

theorem aux_continuous_liftY {N : ℕ} :
    Continuous fun p : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ => liftY p.1 p.2 := by
  unfold liftY
  refine Continuous.matrix_fromBlocks continuous_const ?_ ?_ continuous_snd
  · exact continuous_pi fun _ => continuous_pi fun j => (continuous_apply j).comp continuous_fst
  · exact continuous_pi fun i => continuous_pi fun _ => (continuous_apply i).comp continuous_fst

end RankRedKit

namespace RankRedKit

theorem aux_dot_self_nonneg {n : Type*} [Fintype n] (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

end RankRedKit

namespace RankRedKit

theorem aux_isClosed_imp {α : Type*} [TopologicalSpace α] {P : Prop} {s : Set α}
    (hs : IsClosed s) : IsClosed {p | P → p ∈ s} := by
  by_cases hP : P
  · simpa [hP] using hs
  · simp [hP]

end RankRedKit

namespace RankRedKit

theorem aux_isClosed_posSemidef {n : Type*} [Fintype n] :
    IsClosed {A : Matrix n n ℝ | A.PosSemidef} := by
  have : {A : Matrix n n ℝ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ x : n → ℝ, {A | 0 ≤ star x ⬝ᵥ A *ᵥ x} := by
    ext A; simp only [Set.mem_ofPred_eq, posSemidef_iff_dotProduct_mulVec, IsHermitian,
      Set.mem_inter_iff, Set.mem_iInter]
  rw [this]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

end RankRedKit

namespace RankRedKit

def liftQ {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (c : ℝ) :
    Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) ℝ :=
  Matrix.fromBlocks (fun _ _ => c) (fun _ j => b j) (fun i _ => b i) A

end RankRedKit

namespace RankRedKit

def shorFeasible {N m : ℕ} (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (b : Fin m → Fin N → ℝ)
    (c : Fin m → ℝ) (I : Fin m → Prop) : Set ((Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ) :=
  {p | p.2.IsSymm ∧ (liftY p.1 p.2).PosSemidef ∧
    ∀ i, (I i → (liftQ (A i) (b i) (c i) * liftY p.1 p.2).trace ≤ 0) ∧
      (¬ I i → (liftQ (A i) (b i) (c i) * liftY p.1 p.2).trace = 0)}

end RankRedKit

namespace RankRedKit

theorem aux_isClosed_shorFeasible {N m : ℕ} (A : Fin m → Matrix (Fin N) (Fin N) ℝ)
    (b : Fin m → Fin N → ℝ) (c : Fin m → ℝ) (I : Fin m → Prop) :
    IsClosed (shorFeasible A b c I) := by
  have hY := aux_continuous_liftY (N := N)
  have htr : ∀ i, Continuous fun p : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ =>
      (liftQ (A i) (b i) (c i) * liftY p.1 p.2).trace := fun i =>
    (continuous_const.matrix_mul hY).matrix_trace
  have e : shorFeasible A b c I = {p : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ | p.2ᵀ = p.2} ∩
      ((fun p : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ => liftY p.1 p.2) ⁻¹'
        {M | M.PosSemidef}) ∩
      ⋂ i, ({p | I i → p ∈ {p : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ |
              (liftQ (A i) (b i) (c i) * liftY p.1 p.2).trace ≤ 0}} ∩
            {p | ¬ I i → p ∈ {p : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ |
              (liftQ (A i) (b i) (c i) * liftY p.1 p.2).trace = 0}}) := by
    ext p
    simp only [shorFeasible, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_iInter]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [e]
  refine ((isClosed_eq continuous_snd.matrix_transpose continuous_snd).inter
    (aux_isClosed_posSemidef.preimage hY)).inter (isClosed_iInter fun i => ?_)
  exact (aux_isClosed_imp (isClosed_le (htr i) continuous_const)).inter
    (aux_isClosed_imp (isClosed_eq (htr i) continuous_const))

end RankRedKit

namespace RankRedKit

theorem aux_liftQ_comb {N m : ℕ} (A₀ : Matrix (Fin N) (Fin N) ℝ) (b₀ : Fin N → ℝ) (c₀ : ℝ)
    (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (b : Fin m → Fin N → ℝ) (c : Fin m → ℝ) (γ : Fin m → ℝ) :
    liftQ (A₀ + ∑ i, γ i • A i) (b₀ + ∑ i, γ i • b i) (c₀ + ∑ i, γ i * c i) =
      liftQ A₀ b₀ c₀ + ∑ i, γ i • liftQ (A i) (b i) (c i) := by
  ext (i | i) (j | j) <;> simp [liftQ, Matrix.fromBlocks, Matrix.sum_apply, Finset.sum_apply]

end RankRedKit

end

noncomputable section
open Matrix

theorem aux_lin_le {α c s : ℝ} (h : ∀ R : ℝ, 0 ≤ R → α + R * c ≤ s) : c ≤ 0 := by
  by_contra hc
  push Not at hc
  have h1 := h ((|s - α| + 1) / c) (by positivity)
  rw [div_mul_cancel₀ _ hc.ne'] at h1
  linarith [le_abs_self (s - α)]

end

section
open Matrix

namespace RankRedKit

theorem aux_sq_le_dot {n : Type*} [Fintype n] (v : n → ℝ) (i : n) : v i * v i ≤ v ⬝ᵥ v :=
  Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
    (Finset.mem_univ i)

end RankRedKit

namespace RankRedKit

theorem aux_posDef_coercive {n : Type*} [Fintype n] {G : Matrix n n ℝ} (hG : G.PosDef) :
    ∃ l : ℝ, 0 < l ∧ ∀ v : n → ℝ, l * (v ⬝ᵥ v) ≤ v ⬝ᵥ (G *ᵥ v) := by
  have hpos : ∀ v : n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (G *ᵥ v) := fun v hv => by
    simpa using hG.dotProduct_mulVec_pos hv
  have hnorm : ∀ v : n → ℝ, v ≠ 0 → ∃ c : ℝ, (c • v) ⬝ᵥ (c • v) = 1 ∧ c ^ 2 * (v ⬝ᵥ v) = 1 := by
    intro v hv
    have hvv : 0 < v ⬝ᵥ v :=
      lt_of_le_of_ne (aux_dot_self_nonneg v) (Ne.symm (mt dotProduct_self_eq_zero.1 hv))
    have hs2 : Real.sqrt (v ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hvv.le
    have hs : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.2 hvv
    have h1 : ((Real.sqrt (v ⬝ᵥ v))⁻¹) ^ 2 * (v ⬝ᵥ v) = 1 := by
      rw [inv_pow, hs2, inv_mul_cancel₀ hvv.ne']
    refine ⟨(Real.sqrt (v ⬝ᵥ v))⁻¹, ?_, h1⟩
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← h1]; ring
  let sph : Set (n → ℝ) := {v | v ⬝ᵥ v = 1}
  have hcomp : IsCompact sph := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun v hv => ?_⟩
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 := aux_sq_le_dot v i
      have h2 : v ⬝ᵥ v = 1 := hv
      rw [Real.norm_eq_abs]
      nlinarith [abs_mul_abs_self (v i), abs_nonneg (v i)]
  by_cases hne : sph.Nonempty
  · have hcont : Continuous fun v : n → ℝ => v ⬝ᵥ (G *ᵥ v) :=
      continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
    obtain ⟨v₀, hv₀, hmin⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
    have hv₀ne : v₀ ≠ 0 := by
      rintro rfl; simp [sph] at hv₀
    refine ⟨v₀ ⬝ᵥ (G *ᵥ v₀), hpos v₀ hv₀ne, fun v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    obtain ⟨c, hc1, hc2⟩ := hnorm v hv
    have := isMinOn_iff.mp hmin (c • v) hc1
    have hq : (c • v) ⬝ᵥ (G *ᵥ (c • v)) = c ^ 2 * (v ⬝ᵥ (G *ᵥ v)) := by
      simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring
    rw [hq] at this
    have hvv := aux_dot_self_nonneg v
    have hm : v₀ ⬝ᵥ (G *ᵥ v₀) * (v ⬝ᵥ v) ≤ c ^ 2 * (v ⬝ᵥ (G *ᵥ v)) * (v ⬝ᵥ v) :=
      mul_le_mul_of_nonneg_right this hvv
    calc v₀ ⬝ᵥ (G *ᵥ v₀) * (v ⬝ᵥ v) ≤ c ^ 2 * (v ⬝ᵥ (G *ᵥ v)) * (v ⬝ᵥ v) := hm
      _ = (c ^ 2 * (v ⬝ᵥ v)) * (v ⬝ᵥ (G *ᵥ v)) := by ring
      _ = v ⬝ᵥ (G *ᵥ v) := by rw [hc2, one_mul]
  · refine ⟨1, one_pos, fun v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    obtain ⟨c, hc1, -⟩ := hnorm v hv
    exact absurd ⟨c • v, hc1⟩ hne

end RankRedKit

namespace RankRedKit

theorem posSemidef_eq_sum_vecMulVec {n : Type*} [Fintype n] {Z : Matrix n n ℝ}
    (hZ : Z.PosSemidef) : ∃ z : n → n → ℝ, Z = ∑ j, vecMulVec (z j) (z j) := by
  classical
  open scoped MatrixOrder in
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hZ.nonneg
  refine ⟨fun j => B j, ?_⟩
  ext a b
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply, star_eq_conjTranspose]

end RankRedKit

namespace RankRedKit

theorem aux_psd_entry {n : Type*} [Fintype n] {W : Matrix n n ℝ} (hW : W.PosSemidef) (i j : n) :
    |W i j| ≤ W.trace := by
  obtain ⟨w, rfl⟩ := posSemidef_eq_sum_vecMulVec hW
  have htr : ∀ l, (vecMulVec (w l) (w l)).trace = w l ⬝ᵥ w l := by
    intro l; simp [trace, vecMulVec_apply, dotProduct]
  rw [trace_sum]
  simp only [Matrix.sum_apply, vecMulVec_apply, htr]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  have h1 := aux_sq_le_dot (w l) i
  have h2 := aux_sq_le_dot (w l) j
  rw [abs_mul]
  nlinarith [abs_mul_abs_self (w l i), abs_mul_abs_self (w l j), sq_nonneg (|w l i| - |w l j|)]

end RankRedKit

end

noncomputable section
open Matrix

theorem aux_seg {s t p q : ℝ} (ht : 0 < t) (hs : 0 < s) (hst : s + t = 1)
    (h1 : p ≤ s * p + t * q) (h2 : q ≤ s * p + t * q) : s * p + t * q = p ∧ s * p + t * q = q := by
  have ep : p = s * p + t * p := by rw [← add_mul, hst, one_mul]
  have eq : q = s * q + t * q := by rw [← add_mul, hst, one_mul]
  have hpq : t * p ≤ t * q := by linarith
  have hqp : s * q ≤ s * p := by linarith
  have a1 := le_of_mul_le_mul_left hpq ht
  have a2 := le_of_mul_le_mul_left hqp hs
  have : p = q := le_antisymm a1 a2
  subst this
  constructor <;> linarith

end

section
open Matrix

namespace RankRedKit

theorem aux_sq_expand {N : ℕ} (l : ℝ) (x bb : Fin N → ℝ) :
    0 ≤ l ^ 2 * (x ⬝ᵥ x) + 4 * l * (bb ⬝ᵥ x) + 4 * (bb ⬝ᵥ bb) := by
  have h0 := aux_dot_self_nonneg (l • x + (2 : ℝ) • bb)
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm x bb] at h0
  nlinarith

end RankRedKit

end

noncomputable section
open Matrix

theorem aux_sum_single_mul {m : ℕ} (g : Fin m → ℝ) (i : Fin m) (R : ℝ) :
    ∑ j, (Pi.single i R : Fin m → ℝ) j * g j = R * g i := by
  rw [Fintype.sum_eq_single i (fun j hj => by rw [Pi.single_eq_of_ne hj, zero_mul]),
    Pi.single_eq_same]

theorem aux_sum_single_smul {N m : ℕ} (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (i : Fin m)
    (R : ℝ) : ∑ j, (Pi.single i R : Fin m → ℝ) j • A j = R • A i := by
  rw [Fintype.sum_eq_single i (fun j hj => by rw [Pi.single_eq_of_ne hj, zero_smul]),
    Pi.single_eq_same]

theorem aux_symm_comb {N m : ℕ} (A₀ : Matrix (Fin N) (Fin N) ℝ)
    (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (hA₀ : A₀.IsSymm) (hA : ∀ i, (A i).IsSymm)
    (γ : Fin m → ℝ) : (A₀ + ∑ i, γ i • A i).IsSymm := by
  refine hA₀.add ?_
  unfold Matrix.IsSymm
  rw [transpose_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [transpose_smul, (hA i).eq]

theorem aux_trace_comb {N m : ℕ} (A₀ : Matrix (Fin N) (Fin N) ℝ)
    (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (γ : Fin m → ℝ) (W : Matrix (Fin N) (Fin N) ℝ) :
    ((A₀ + ∑ i, γ i • A i) * W).trace = (A₀ * W).trace + ∑ i, γ i * (A i * W).trace := by
  rw [add_mul, trace_add, Finset.sum_mul, trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

end

section
open Matrix

namespace RankRedKit

theorem aux_trace_vecMulVec {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    (M * vecMulVec x x).trace = x ⬝ᵥ M *ᵥ x := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end RankRedKit

namespace RankRedKit

theorem aux_trace_lower {n : Type*} [Fintype n] {G W : Matrix n n ℝ} {l : ℝ}
    (hl : ∀ v : n → ℝ, l * (v ⬝ᵥ v) ≤ v ⬝ᵥ (G *ᵥ v)) (hW : W.PosSemidef) :
    l * W.trace ≤ (G * W).trace := by
  obtain ⟨w, rfl⟩ := posSemidef_eq_sum_vecMulVec hW
  rw [Matrix.mul_sum, trace_sum, trace_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : (vecMulVec (w j) (w j)).trace = w j ⬝ᵥ w j := by
    simp [trace, vecMulVec_apply, dotProduct]
  rw [h1, aux_trace_vecMulVec]
  exact hl _

end RankRedKit

namespace RankRedKit

theorem aux_vecMulVec_isSymm {N : ℕ} (x : Fin N → ℝ) : (vecMulVec x x).IsSymm := by
  show (vecMulVec x x)ᵀ = vecMulVec x x
  ext i j; simp [vecMulVec_apply, mul_comm]

end RankRedKit

end

noncomputable section
open Matrix QCQPTightness.Exact

theorem dot_Aγ {N m : ℕ} (P : QCQP N m) (γ : Fin m → ℝ) (y z : Fin N → ℝ) :
    z ⬝ᵥ (P.Aγ γ *ᵥ y) = z ⬝ᵥ (P.A₀ *ᵥ y) + ∑ i, γ i * (z ⬝ᵥ (P.A i *ᵥ y)) := by
  simp only [QCQP.Aγ, add_mulVec, sum_mulVec, smul_mulVec, dotProduct_add, dotProduct_sum,
    dotProduct_smul, smul_eq_mul]

theorem dot_bγ {N m : ℕ} (P : QCQP N m) (γ : Fin m → ℝ) (z : Fin N → ℝ) :
    P.bγ γ ⬝ᵥ z = P.b₀ ⬝ᵥ z + ∑ i, γ i * (P.b i ⬝ᵥ z) := by
  simp only [QCQP.bγ, add_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul]

end

section
open Matrix

namespace RankRedKit

def quad {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (c : ℝ) (x : Fin N → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x) + 2 * (b ⬝ᵥ x) + c

end RankRedKit

namespace RankRedKit

theorem quad_add {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm) (b : Fin N → ℝ) (c : ℝ)
    (x w : Fin N → ℝ) :
    quad A b c (x + w) = quad A b c x + 2 * ((A *ᵥ x + b) ⬝ᵥ w) + w ⬝ᵥ (A *ᵥ w) := by
  have h1 : x ⬝ᵥ (A *ᵥ w) = (A *ᵥ x) ⬝ᵥ w := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq, dotProduct_comm]
  simp only [quad, mulVec_add, dotProduct_add, add_dotProduct, h1]
  rw [dotProduct_comm w (A *ᵥ x)]
  ring

end RankRedKit

end

noncomputable section
open Matrix QCQPTightness.Exact

theorem quad_line {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm) (b : Fin N → ℝ) (c : ℝ)
    (y z : Fin N → ℝ) (s : ℝ) :
    QCQPTightness.ConvHull.quad A b c (y + s • z) = QCQPTightness.ConvHull.quad A b c y +
      s * (2 * (y ⬝ᵥ (A *ᵥ z) + b ⬝ᵥ z)) + s ^ 2 * (z ⬝ᵥ (A *ᵥ z)) := by
  have h := RankRedKit.quad_add hA b c y (s • z)
  have h1 : y ⬝ᵥ (A *ᵥ z) = (A *ᵥ y) ⬝ᵥ z := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq, dotProduct_comm]
  change QCQPTightness.ConvHull.quad A b c (y + s • z) = QCQPTightness.ConvHull.quad A b c y +
      2 * ((A *ᵥ y + b) ⬝ᵥ (s • z)) + (s • z) ⬝ᵥ (A *ᵥ (s • z)) at h
  rw [h, h1]
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, add_dotProduct, smul_eq_mul]
  ring

theorem qγ_eq {N m : ℕ} (P : QCQP N m) (γ : Fin m → ℝ) (x : Fin N → ℝ) :
    P.qγ γ x = P.q₀ x + (fun i => P.q i x) ⬝ᵥ γ := by
  simp only [QCQP.qγ, dotProduct]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem descent {N m p : ℕ} (P : QCQP N m) (a : Fin p → Fin m → ℝ) (β : Fin p → ℝ)
    (hΓ : P.Gamma = poly a β) (x v : Fin N → ℝ) (γh : Fin m → ℝ)
    (hγh : γh ∈ argmaxOn (poly a β) (fun i => P.q i x))
    (hker : ∀ γ ∈ argmaxOn (poly a β) (fun i => P.q i x), P.Aγ γ *ᵥ v = 0)
    (hbv : ∀ γ ∈ argmaxOn (poly a β) (fun i => P.q i x), P.bγ γ ⬝ᵥ v ≤ -1) :
    ∃ α : ℝ, 0 < α ∧ ∀ γ ∈ P.Gamma, P.qγ γ (x + α • v) ≤ P.qγ γh x - 2 * α := by
  set u : Fin m → ℝ := fun i => P.q i x with hu
  set F := argmaxOn (poly a β) u with hF
  let e₁ : ℝ := 2 * (x ⬝ᵥ (P.A₀ *ᵥ v) + P.b₀ ⬝ᵥ v)
  let e₂ : ℝ := v ⬝ᵥ (P.A₀ *ᵥ v)
  let w₁ : Fin m → ℝ := fun i => 2 * (x ⬝ᵥ (P.A i *ᵥ v) + P.b i ⬝ᵥ v)
  let w₂ : Fin m → ℝ := fun i => v ⬝ᵥ (P.A i *ᵥ v)
  -- the line expansion
  have hline : ∀ (s : ℝ) (γ : Fin m → ℝ), P.qγ γ (x + s • v) =
      P.q₀ x + s * e₁ + s ^ 2 * e₂ + (u ⬝ᵥ γ + s * (w₁ ⬝ᵥ γ) + s ^ 2 * (w₂ ⬝ᵥ γ)) := by
    intro s γ
    rw [qγ_eq]
    have h0 : P.q₀ (x + s • v) = P.q₀ x + s * e₁ + s ^ 2 * e₂ :=
      quad_line P.A₀_symm P.b₀ P.c₀ x v s
    have hi : (fun i => P.q i (x + s • v)) = fun i => u i + s * w₁ i + s ^ 2 * w₂ i := by
      funext i; exact quad_line (P.A_symm i) (P.b i) (P.c i) x v s
    rw [h0, hi]
    simp only [dotProduct, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  -- coefficients on the face
  have hc1 : ∀ γ ∈ F, w₁ ⬝ᵥ γ ≤ -2 - e₁ := by
    intro γ hγ
    have h1 := dot_Aγ P γ v x
    have h2 := dot_bγ P γ v
    rw [hker γ hγ, dotProduct_zero] at h1
    have h3 := hbv γ hγ
    have hw : w₁ ⬝ᵥ γ = 2 * ∑ i, γ i * (x ⬝ᵥ (P.A i *ᵥ v)) + 2 * ∑ i, γ i * (P.b i ⬝ᵥ v) := by
      show ∑ i, w₁ i * γ i = _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [w₁]; ring
    rw [hw]; simp only [e₁]; linarith
  have hc2 : ∀ γ ∈ F, w₂ ⬝ᵥ γ ≤ -e₂ := by
    intro γ hγ
    have h1 := dot_Aγ P γ v v
    rw [hker γ hγ, dotProduct_zero] at h1
    have : w₂ ⬝ᵥ γ = ∑ i, γ i * (v ⬝ᵥ (P.A i *ᵥ v)) := by
      simp only [w₂, dotProduct]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this]; simp only [e₂]; linarith
  have hne : F.Nonempty := ⟨γh, hγh⟩
  obtain ⟨δ, hδ, hpert⟩ := argmaxOn_perturb a β u hne ![w₁, w₂] ![-2 - e₁, -e₂]
    (by intro k; fin_cases k
        · exact hc1
        · exact hc2)
  refine ⟨min δ 1, lt_min hδ one_pos, fun γ hγ => ?_⟩
  set α := min δ 1 with hα
  have hα0 : 0 < α := lt_min hδ one_pos
  have hαδ : α ≤ δ := min_le_left _ _
  have hα1 : α ≤ 1 := min_le_right _ _
  have hα2 : α ^ 2 ≤ α := by nlinarith
  have hγ' : γ ∈ poly a β := hΓ ▸ hγ
  have key := hpert ![α, α ^ 2]
    (by intro k; fin_cases k
        · exact ⟨hα0.le, hαδ⟩
        · exact ⟨sq_nonneg _, hα2.trans hαδ⟩) γh hγh γ hγ'
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    add_dotProduct, smul_dotProduct, smul_eq_mul] at key
  rw [hline α γ]
  have hh : P.qγ γh x = P.q₀ x + u ⬝ᵥ γh := qγ_eq P γh x
  rw [hh]
  linarith

theorem isSymm_of_posSemidef {N : ℕ} {W : Matrix (Fin N) (Fin N) ℝ} (hW : W.PosSemidef) :
    W.IsSymm := by
  have h := hW.isHermitian
  simpa [Matrix.IsSymm, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using h

end

section
open Matrix

namespace RankRedKit

theorem liftY_posSemidef_iff {N : ℕ} (x : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    (liftY x X).PosSemidef ↔ (X - vecMulVec x x).PosSemidef := by
  let B : Matrix (Fin 1) (Fin N) ℝ := Matrix.of fun _ j => x j
  have hB : liftY x X = fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) B Bᴴ X := by
    unfold liftY; congr 1
    · ext i j; fin_cases i; fin_cases j; rfl
  have hS : Bᴴ * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * B = vecMulVec x x := by
    ext i j; simp [B, Matrix.mul_apply, vecMulVec_apply]
  let _ : Invertible (1 : Matrix (Fin 1) (Fin 1) ℝ) := invertibleOne
  rw [hB, ← hS]
  exact PosDef.fromBlocks₁₁ _ _ PosDef.one

end RankRedKit

end

noncomputable section
open Matrix QCQPTightness.Exact

theorem liftY_psd_iff {N : ℕ} (x : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    (QCQPTightness.ConvHull.liftY x X).PosSemidef ↔ (X - vecMulVec x x).PosSemidef :=
  RankRedKit.liftY_posSemidef_iff x X

end

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem exists_lagrange_multiplier {X F : Type*}
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [T2Space F] [FiniteDimensional ℝ F]
    (S : Set X) (f : X → ℝ) (G : X → F) (K : PointedCone ℝ F)
    -- Fan convexlike: mixtures stay in `S`, improve `f`, and stay at least as feasible
    (hcvx : ∀ x₁ ∈ S, ∀ x₂ ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ x ∈ S,
        G x - (t • G x₁ + (1 - t) • G x₂) ∈ K ∧ t * f x₁ + (1 - t) * f x₂ ≤ f x)
    -- generalized Slater: perturbation domain contains a neighbourhood of 0
    -- (this covers equalities, K = ⊥, via "moment vector in the interior")
    (hslater : (0 : F) ∈ interior {u | ∃ x ∈ S, G x - u ∈ K})
    (p : ℝ) (hp : ∀ x ∈ S, G x ∈ K → f x ≤ p) :
    ∃ y : Module.Dual ℝ F, (∀ k ∈ K, 0 ≤ y k) ∧ ∀ x ∈ S, f x + y (G x) ≤ p := by
  classical
  set U : Set F := {u | ∃ x ∈ S, G x - u ∈ K} with hUdef
  have hU : U ∈ nhds (0 : F) := mem_interior_iff_mem_nhds.1 hslater
  set D : Set (F × ℝ) := {q | ∃ x ∈ S, G x - q.1 ∈ K ∧ q.2 < f x - p} with hDdef
  -- convexity of D
  have hDconv : Convex ℝ D := by
    rintro ⟨u₁, s₁⟩ ⟨x₁, hx₁, hK₁, hs₁⟩ ⟨u₂, s₂⟩ ⟨x₂, hx₂, hK₂, hs₂⟩ a b ha hb hab
    obtain ⟨x, hx, hKx, hfx⟩ := hcvx x₁ hx₁ x₂ hx₂ a ha (by linarith)
    have hb' : b = 1 - a := by linarith
    subst hb'
    refine ⟨x, hx, ?_, ?_⟩
    · have e : G x - (a • u₁ + (1 - a) • u₂) = (G x - (a • G x₁ + (1 - a) • G x₂)) +
          (a • (G x₁ - u₁) + (1 - a) • (G x₂ - u₂)) := by
        simp only [smul_sub]; abel
      simp only [Prod.fst_add, Prod.smul_fst]
      rw [e]
      exact K.add_mem hKx (K.add_mem (PointedCone.smul_mem K ha hK₁) (PointedCone.smul_mem K hb hK₂))
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      simp only at hs₁ hs₂
      rcases ha.eq_or_lt with ha0 | ha0
      · subst ha0; linarith
      · have h1 : a * s₁ < a * (f x₁ - p) := mul_lt_mul_of_pos_left hs₁ ha0
        have h2 : (1 - a) * s₂ ≤ (1 - a) * (f x₂ - p) := mul_le_mul_of_nonneg_left hs₂.le hb
        nlinarith
  -- D is downward closed and has points over U
  have hDdown : ∀ u s s', (u, s) ∈ D → s' ≤ s → (u, s') ∈ D := by
    rintro u s s' ⟨x, hx, hK, hs⟩ hle
    exact ⟨x, hx, hK, lt_of_le_of_lt hle hs⟩
  have hDU : ∀ u ∈ U, ∃ s, (u, s) ∈ D := by
    rintro u ⟨x, hx, hK⟩
    exact ⟨f x - p - 1, x, hx, hK, by simp⟩
  -- absorbing
  have habs : ∀ v : F, ∃ c : ℝ, 0 < c ∧ c • v ∈ U ∧ (-c) • v ∈ U := by
    intro v
    have ht : Filter.Tendsto (fun t : ℝ => t • v) (nhds 0) (nhds 0) := by
      exact (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • v).tendsto' 0 0
        (zero_smul ℝ v)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (ht hU)
    refine ⟨ε / 2, by positivity, hball ?_, hball ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]; linarith
  obtain ⟨s₀, hs₀⟩ := hDU 0 (mem_of_mem_nhds hU)
  -- affine span of D is everything
  have hspan : affineSpan ℝ D = ⊤ := by
    have hne : (affineSpan ℝ D : Set (F × ℝ)).Nonempty := ⟨_, subset_affineSpan ℝ D hs₀⟩
    rw [← AffineSubspace.direction_eq_top_iff_of_nonempty hne, direction_affineSpan, eq_top_iff]
    rintro ⟨v, r⟩ -
    have e01 : ((0 : F), (1 : ℝ)) ∈ vectorSpan ℝ D := by
      have := vsub_mem_vectorSpan ℝ hs₀ (hDdown 0 s₀ (s₀ - 1) hs₀ (by linarith))
      simpa using this
    have hu0 : ∀ u ∈ U, ((u : F), (0 : ℝ)) ∈ vectorSpan ℝ D := by
      intro u hu
      obtain ⟨s, hs⟩ := hDU u hu
      have h1 := vsub_mem_vectorSpan ℝ hs hs₀
      have h2 := (vectorSpan ℝ D).smul_mem (s - s₀) e01
      have h3 := (vectorSpan ℝ D).sub_mem h1 h2
      convert h3 using 1
      ext <;> simp
    obtain ⟨c, hc, hcv, -⟩ := habs v
    have h3 := (vectorSpan ℝ D).smul_mem c⁻¹ (hu0 _ hcv)
    have h4 := (vectorSpan ℝ D).smul_mem r e01
    have h5 := (vectorSpan ℝ D).add_mem h3 h4
    convert h5 using 1
    ext <;> simp [smul_smul, inv_mul_cancel₀ hc.ne']
  have hint : (interior D).Nonempty := aux2_interior_nonempty hDconv hspan
  have hnot : ((0 : F), (0 : ℝ)) ∉ interior D := by
    intro h
    obtain ⟨x, hx, hK, hlt⟩ := interior_subset h
    simp only [sub_zero] at hK hlt
    linarith [hp x hx hK]
  obtain ⟨φ, hφne, hφ⟩ := geometric_hahn_banach_of_nonempty_interior_point hDconv hnot hint
  have hφ0 : φ ((0 : F), (0 : ℝ)) = 0 := by
    rw [show ((0 : F), (0 : ℝ)) = 0 from rfl, map_zero]
  set μ := φ ((0 : F), (1 : ℝ)) with hμdef
  have hdec : ∀ (u : F) (s : ℝ), φ (u, s) = φ (u, 0) + s * μ := by
    intro u s
    rw [hμdef, ← smul_eq_mul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have hD' : ∀ u s, (u, s) ∈ D → φ (u, 0) + s * μ ≤ 0 := by
    intro u s h
    rw [← hdec, ← hφ0]
    exact hφ _ h
  -- μ ≥ 0
  have hμ0 : 0 ≤ μ := by
    have := aux2_lin_nonneg μ (φ (0, 0) + s₀ * μ) fun t ht => by
      have := hD' 0 (s₀ - t) (hDdown 0 s₀ _ hs₀ (by linarith))
      linarith
    exact this
  -- μ ≠ 0
  have hμpos : 0 < μ := by
    refine lt_of_le_of_ne hμ0 fun hμz => hφne ?_
    have hlam : ∀ u ∈ U, φ (u, 0) ≤ 0 := by
      intro u hu
      obtain ⟨s, hs⟩ := hDU u hu
      have := hD' u s hs
      rw [← hμz, mul_zero, add_zero] at this
      exact this
    have hzero : ∀ v : F, φ (v, 0) = 0 := by
      intro v
      obtain ⟨c, hc, h1, h2⟩ := habs v
      have e1 : φ (c • v, 0) = c * φ (v, 0) := by
        rw [← smul_eq_mul, ← map_smul]; congr 1; ext <;> simp
      have e2 : φ ((-c) • v, 0) = -c * φ (v, 0) := by
        rw [← smul_eq_mul, ← map_smul]; congr 1; ext <;> simp
      have a1 := hlam _ h1
      have a2 := hlam _ h2
      rw [e1] at a1
      rw [e2] at a2
      have : φ (v, 0) ≤ 0 := by
        by_contra h; push Not at h; nlinarith
      have : 0 ≤ φ (v, 0) := by
        by_contra h; push Not at h; nlinarith
      linarith
    refine ContinuousLinearMap.ext fun q => ?_
    obtain ⟨v, s⟩ := q
    rw [hdec, hzero, ← hμz]
    simp
  -- the multiplier
  let y : Module.Dual ℝ F := μ⁻¹ • ((φ : F × ℝ →ₗ[ℝ] ℝ).comp (LinearMap.inl ℝ F ℝ))
  have hy : ∀ u, y u = μ⁻¹ * φ (u, 0) := fun u => rfl
  refine ⟨y, fun k hk => ?_, fun x hx => ?_⟩
  · rw [hy]
    refine mul_nonneg (inv_nonneg.2 hμ0) ?_
    obtain ⟨x₀', hx₀', hK₀⟩ := (show (0 : F) ∈ U from mem_of_mem_nhds hU)
    refine aux2_lin_nonneg _ ((f x₀' - p - 1) * μ) fun t ht => ?_
    have hmem : ((-t) • k, f x₀' - p - 1) ∈ D := by
      refine ⟨x₀', hx₀', ?_, by simp⟩
      have : G x₀' - (-t) • k = (G x₀' - 0) + t • k := by simp [neg_smul]
      rw [this]
      exact K.add_mem hK₀ (PointedCone.smul_mem K ht hk)
    have := hD' _ _ hmem
    have e : φ ((-t) • k, 0) = -t * φ (k, 0) := by
      rw [← smul_eq_mul, ← map_smul]; congr 1; ext <;> simp
    rw [e] at this
    linarith
  · have hlim := aux2_lim (φ (G x, 0)) (f x - p) μ hμpos fun s hs => hD' _ _ ⟨x, hx, by simp, hs⟩
    rw [hy]
    have : μ⁻¹ * φ (G x, 0) ≤ -(f x - p) := by
      rw [inv_mul_le_iff₀ hμpos]; linarith
    linarith

theorem Matrix.PosDef.mem_interior_psdForm {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    A ∈ interior (psdForm n : Set (Matrix n n ℝ)) := by
  rw [mem_interior_iff_mem_nhds]
  have hpos : ∀ v ∈ aux2_sph n, 0 < v ⬝ᵥ A *ᵥ v := fun v hv => by
    simpa using hA.dotProduct_mulVec_pos (aux2_sph_ne hv)
  have hcont : Continuous (fun z : Matrix n n ℝ × (n → ℝ) => z.2 ⬝ᵥ z.1 *ᵥ z.2) :=
    continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
  have hev := (aux2_sph_compact n).eventually_forall_of_forall_eventually (x₀ := A)
    (P := fun B v => 0 < v ⬝ᵥ B *ᵥ v)
    (fun v hv => hcont.continuousAt.eventually (lt_mem_nhds (hpos v hv)))
  filter_upwards [hev] with B hB
  intro v
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨c, hc, hcv⟩ := aux2_normalize hv
  have h := hB _ hcv
  rw [aux2_qf_smul] at h
  exact (pos_of_mul_pos_right h (sq_nonneg c)).le

theorem mem_psdForm_iff_posSemidef {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.IsSymm) :
    A ∈ psdForm n ↔ A.PosSemidef := by
  rw [aux2_mem_psdForm, posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h; exact ⟨aux2_isHermitian hA, fun x => by simpa using h x⟩
  · rintro ⟨-, h⟩ v; simpa using h v

theorem psdForm_dual {n : Type*} [Fintype n] [DecidableEq n] (y : Module.Dual ℝ (Matrix n n ℝ))
    (hy : ∀ A ∈ psdForm n, 0 ≤ y A) : ∃ Y : Matrix n n ℝ, Y.PosSemidef ∧ ∀ A, y A = (Yᵀ * A).trace := by
  let Y : Matrix n n ℝ := fun i j => y (Matrix.single i j 1)
  have hrep : ∀ A, y A = (Yᵀ * A).trace := by
    intro A
    conv_lhs => rw [matrix_eq_sum_single A]
    have hs : ∀ i j, y (Matrix.single i j (A i j)) = A i j * Y i j := by
      intro i j
      have : Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℝ) := by
        rw [smul_single, smul_eq_mul, mul_one]
      rw [this, map_smul, smul_eq_mul]
    simp only [map_sum, hs, trace, diag, mul_apply, transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hanti : ∀ i j, Matrix.single i j (1 : ℝ) - Matrix.single j i 1 ∈ psdForm n := by
    intro i j v
    have : v ⬝ᵥ (Matrix.single i j (1 : ℝ) - Matrix.single j i 1) *ᵥ v = 0 := by
      simp only [sub_mulVec, dotProduct_sub, single_mulVec, one_mul]
      change v ⬝ᵥ Pi.single i (v j) - v ⬝ᵥ Pi.single j (v i) = 0
      simp only [dotProduct_single]
      ring
    rw [this]
  have hsymm : Yᵀ = Y := by
    ext i j
    have h1 := hy _ (hanti i j)
    have h2 := hy _ (hanti j i)
    simp only [map_sub] at h1 h2
    show y (Matrix.single j i 1) = y (Matrix.single i j 1)
    linarith
  refine ⟨Y, ?_, hrep⟩
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · exact aux2_isHermitian hsymm
  · have h := hy _ (aux2_vecMulVec_mem x)
    rw [hrep, aux2_trace_vecMulVec, hsymm] at h
    simpa using h

theorem Matrix.PosSemidef.trace_mul_nonneg {n : Type*} [Fintype n] {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := aux2_trace_mul_nonneg hA hB

end

noncomputable section
open Matrix

theorem psd_dual_description {N m : ℕ} (A₀ : Matrix (Fin N) (Fin N) ℝ)
    (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (hA₀ : A₀.IsSymm) (hA : ∀ i, (A i).IsSymm)
    (I : Fin m → Prop) (γs : Fin m → ℝ) (hγs : ∀ i, I i → 0 ≤ γs i)
    (hPD : (A₀ + ∑ i, γs i • A i).PosDef) (f₀ : ℝ) (f : Fin m → ℝ) (s : ℝ) :
    (∃ W : Matrix (Fin N) (Fin N) ℝ, W.PosSemidef ∧ f₀ + (A₀ * W).trace ≤ s ∧
        ∀ i, (I i → f i + (A i * W).trace ≤ 0) ∧ (¬ I i → f i + (A i * W).trace = 0)) ↔
      ∀ γ : Fin m → ℝ, (A₀ + ∑ i, γ i • A i).PosSemidef → (∀ i, I i → 0 ≤ γ i) →
        f₀ + ∑ i, γ i * f i ≤ s := by
  classical
  constructor
  · rintro ⟨W, hW, h0, hi⟩ γ hγ hγI
    have htr := Matrix.PosSemidef.trace_mul_nonneg hγ hW
    rw [aux_trace_comb] at htr
    have hterm : ∀ i, γ i * (f i + (A i * W).trace) ≤ 0 := by
      intro i
      by_cases hI : I i
      · exact mul_nonpos_of_nonneg_of_nonpos (hγI i hI) ((hi i).1 hI)
      · rw [(hi i).2 hI, mul_zero]
    have hs := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hterm i
    have e : ∑ i, γ i * (f i + (A i * W).trace) =
        ∑ i, γ i * f i + ∑ i, γ i * (A i * W).trace := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  · intro hall
    let S : Set (Fin m → ℝ) := {γ | ∀ i, I i → 0 ≤ γ i}
    let fF : (Fin m → ℝ) → ℝ := fun γ => f₀ + ∑ i, γ i * f i
    let G : (Fin m → ℝ) → Matrix (Fin N) (Fin N) ℝ := fun γ => A₀ + ∑ i, γ i • A i
    have hcvx : ∀ x₁ ∈ S, ∀ x₂ ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ x ∈ S,
        G x - (t • G x₁ + (1 - t) • G x₂) ∈ psdForm (Fin N) ∧
          t * fF x₁ + (1 - t) * fF x₂ ≤ fF x := by
      intro x₁ h₁ x₂ h₂ t ht0 ht1
      refine ⟨t • x₁ + (1 - t) • x₂, fun i hi => ?_, ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg ht0 (h₁ i hi)) (mul_nonneg (by linarith) (h₂ i hi))
      · have : G (t • x₁ + (1 - t) • x₂) - (t • G x₁ + (1 - t) • G x₂) = 0 := by
          simp only [G, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
            Finset.sum_add_distrib, ← Finset.smul_sum]
          module
        rw [this]
        exact (psdForm (Fin N)).zero_mem
      · simp only [fF, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
          mul_assoc, ← Finset.mul_sum]
        apply le_of_eq
        ring
    have hslater : (0 : Matrix (Fin N) (Fin N) ℝ) ∈
        interior {U | ∃ x ∈ S, G x - U ∈ psdForm (Fin N)} := by
      have hint := Matrix.PosDef.mem_interior_psdForm hPD
      rw [mem_interior_iff_mem_nhds] at hint ⊢
      have hc : ContinuousAt (fun U : Matrix (Fin N) (Fin N) ℝ => G γs - U) 0 :=
        (continuous_const.sub continuous_id).continuousAt
      have : (fun U => G γs - U) ⁻¹' (psdForm (Fin N) : Set (Matrix (Fin N) (Fin N) ℝ)) ∈
          nhds (0 : Matrix (Fin N) (Fin N) ℝ) :=
        hc.preimage_mem_nhds (by rw [sub_zero]; exact hint)
      exact Filter.mem_of_superset this fun U hU => ⟨γs, hγs, hU⟩
    have hp : ∀ x ∈ S, G x ∈ psdForm (Fin N) → fF x ≤ s := by
      intro x hx hG
      exact hall x ((mem_psdForm_iff_posSemidef (aux_symm_comb A₀ A hA₀ hA x)).1 hG) hx
    obtain ⟨y, hy, hyS⟩ :=
      exists_lagrange_multiplier S fF G (psdForm (Fin N)) hcvx hslater s hp
    obtain ⟨Y, hY, hYrep⟩ := psdForm_dual y hy
    have hval : ∀ γ ∈ S,
        f₀ + (A₀ * Yᵀ).trace + ∑ i, γ i * (f i + (A i * Yᵀ).trace) ≤ s := by
      intro γ hγ
      have := hyS γ hγ
      simp only [fF, G] at this
      rw [hYrep, trace_mul_comm, aux_trace_comb] at this
      have e : ∑ i, γ i * (f i + (A i * Yᵀ).trace) =
          ∑ i, γ i * f i + ∑ i, γ i * (A i * Yᵀ).trace := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      linarith
    refine ⟨Yᵀ, hY.transpose, ?_, fun i => ⟨fun hI => ?_, fun hI => ?_⟩⟩
    · simpa using hval 0 (fun i _ => le_rfl)
    · refine aux_lin_le (α := f₀ + (A₀ * Yᵀ).trace) (s := s) fun R hR => ?_
      have := hval (Pi.single i R) (fun j hj => by
        by_cases hji : j = i
        · rw [hji, Pi.single_eq_same]; exact hR
        · rw [Pi.single_eq_of_ne hji])
      rwa [aux_sum_single_mul] at this
    · have hS : ∀ R : ℝ, Pi.single i R ∈ S := fun R j hj => by
        have hji : j ≠ i := fun h => hI (h ▸ hj)
        rw [Pi.single_eq_of_ne hji]
      have h1 : f i + (A i * Yᵀ).trace ≤ 0 :=
        aux_lin_le (α := f₀ + (A₀ * Yᵀ).trace) (s := s) fun R _ => by
          have := hval _ (hS R)
          rwa [aux_sum_single_mul] at this
      have h2 : -(f i + (A i * Yᵀ).trace) ≤ 0 :=
        aux_lin_le (α := f₀ + (A₀ * Yᵀ).trace) (s := s) fun R _ => by
          have := hval _ (hS (-R))
          rw [aux_sum_single_mul] at this
          linarith
      linarith

end

section
open Matrix

namespace RankRedKit

theorem trace_liftQ_mul_liftY {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (c : ℝ)
    (x : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    (liftQ A b c * liftY x X).trace = quad A b c x + (A * (X - vecMulVec x x)).trace := by
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_sum_type, liftQ, liftY, quad, dotProduct,
    Matrix.fromBlocks, Finset.sum_add_distrib, mulVec, vecMulVec_apply, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  have key : ∑ i, ∑ j, x i * (A i j * x j) = ∑ i, ∑ j, A i j * (x j * x i) :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have key2 : ∑ i, 2 * (b i * x i) = 2 * ∑ i, b i * x i := by rw [Finset.mul_sum]
  linarith

end RankRedKit

end

noncomputable section
open Matrix QCQPTightness.Exact

theorem trace_eq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (c : ℝ)
    (x : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    (QCQPTightness.ConvHull.liftQ A b c * QCQPTightness.ConvHull.liftY x X).trace =
      QCQPTightness.ConvHull.quad A b c x + (A * (X - vecMulVec x x)).trace :=
  RankRedKit.trace_liftQ_mul_liftY A b c x X

theorem dsdp_iff {N m : ℕ} (P : QCQP N m) (γs : Fin m → ℝ) (hγs : ∀ i, P.IsIneq i → 0 ≤ γs i)
    (hPD : (P.Aγ γs).PosDef) (x : Fin N → ℝ) (t : ℝ) :
    (x, t) ∈ P.DSDP ↔ ∀ γ ∈ P.Gamma, P.qγ γ x ≤ 2 * t := by
  have key := psd_dual_description P.A₀ P.A P.A₀_symm P.A_symm P.IsIneq γs hγs hPD
    (P.q₀ x) (fun i => P.q i x) (2 * t)
  have hR : (∀ γ ∈ P.Gamma, P.qγ γ x ≤ 2 * t) ↔
      ∀ γ : Fin m → ℝ, (P.A₀ + ∑ i, γ i • P.A i).PosSemidef → (∀ i, P.IsIneq i → 0 ≤ γ i) →
        P.q₀ x + ∑ i, γ i * P.q i x ≤ 2 * t :=
    ⟨fun h γ h1 h2 => h γ ⟨h1, h2⟩, fun h γ hγ => h γ hγ.1 hγ.2⟩
  rw [hR, ← key]
  constructor
  · rintro ⟨X, ⟨_, hY, hc⟩, hobj⟩
    dsimp only at hobj hY hc
    refine ⟨X - vecMulVec x x, (liftY_psd_iff x X).1 hY, ?_, fun i => ?_⟩
    · have := trace_eq P.A₀ P.b₀ P.c₀ x X
      rw [this] at hobj; exact hobj
    · have := trace_eq (P.A i) (P.b i) (P.c i) x X
      have hci := hc i
      rw [this] at hci
      exact hci
  · rintro ⟨W, hW, hobj, hc⟩
    have hX : W + vecMulVec x x - vecMulVec x x = W := add_sub_cancel_right _ _
    refine ⟨W + vecMulVec x x, ⟨?_, ?_, fun i => ?_⟩, ?_⟩
    · exact (isSymm_of_posSemidef hW).add (RankRedKit.aux_vecMulVec_isSymm x)
    · show (QCQPTightness.ConvHull.liftY x (W + vecMulVec x x)).PosSemidef
      rw [liftY_psd_iff, hX]; exact hW
    · show (_ → (QCQPTightness.ConvHull.liftQ (P.A i) (P.b i) (P.c i) *
          QCQPTightness.ConvHull.liftY x (W + vecMulVec x x)).trace ≤ 0) ∧
        (_ → (QCQPTightness.ConvHull.liftQ (P.A i) (P.b i) (P.c i) *
          QCQPTightness.ConvHull.liftY x (W + vecMulVec x x)).trace = 0)
      rw [trace_eq, hX]
      exact hc i
    · show (QCQPTightness.ConvHull.liftQ P.A₀ P.b₀ P.c₀ *
          QCQPTightness.ConvHull.liftY x (W + vecMulVec x x)).trace ≤ 2 * t
      rw [trace_eq, hX]; exact hobj

end

noncomputable section
open Matrix

theorem exists_dotProduct_le_neg_one {N m p : ℕ} (a : Fin p → Fin m → ℝ) (β : Fin p → ℝ)
    (b₀ : Fin N → ℝ) (B : Fin m → Fin N → ℝ) (V : Submodule ℝ (Fin N → ℝ))
    (h : ∀ γ ∈ poly a β, ∃ v ∈ V, (b₀ + ∑ i, γ i • B i) ⬝ᵥ v ≠ 0) :
    ∃ v ∈ V, ∀ γ ∈ poly a β, (b₀ + ∑ i, γ i • B i) ⬝ᵥ v ≤ -1 := by
  classical
  let P1 : (↥V × (Fin p → ℝ)) →ₗ[ℝ] (Fin N → ℝ) := V.subtype ∘ₗ LinearMap.fst ℝ ↥V (Fin p → ℝ)
  let P2 : (↥V × (Fin p → ℝ)) →ₗ[ℝ] (Fin p → ℝ) := LinearMap.snd ℝ ↥V (Fin p → ℝ)
  let ai : Option (Fin p) → Module.Dual ℝ (↥V × (Fin p → ℝ)) := fun o =>
    o.elim ((aux1_dotL b₀) ∘ₗ P1 + (aux1_dotL β) ∘ₗ P2)
      (fun j => -((LinearMap.proj j : (Fin p → ℝ) →ₗ[ℝ] ℝ) ∘ₗ P2))
  let bi : Option (Fin p) → ℝ := fun o => o.elim (-1) (fun _ => 0)
  let ei : Fin m → Module.Dual ℝ (↥V × (Fin p → ℝ)) := fun i =>
    (aux1_dotL (fun j => a j i)) ∘ₗ P2 - (aux1_dotL (B i)) ∘ₗ P1
  let di : Fin m → ℝ := fun _ => 0
  have hai_none : ∀ x, ai none x = b₀ ⬝ᵥ (x.1 : Fin N → ℝ) + β ⬝ᵥ x.2 := fun x => rfl
  have hai_some : ∀ j x, ai (some j) x = -(x.2 j) := fun j x => rfl
  have hei : ∀ i x, ei i x = (fun j => a j i) ⬝ᵥ x.2 - B i ⬝ᵥ (x.1 : Fin N → ℝ) :=
    fun i x => rfl
  by_cases hfeas : ∃ x : ↥V × (Fin p → ℝ), (∀ o, ai o x ≤ bi o) ∧ ∀ i, ei i x = di i
  · obtain ⟨x, h1, h2⟩ := hfeas
    have hn : b₀ ⬝ᵥ (x.1 : Fin N → ℝ) + β ⬝ᵥ x.2 ≤ -1 := by
      rw [← hai_none]
      exact h1 none
    have hs : ∀ j, 0 ≤ x.2 j := fun j => by
      have := h1 (some j)
      rw [hai_some] at this
      exact neg_nonpos.1 this
    have he : ∀ i, B i ⬝ᵥ (x.1 : Fin N → ℝ) = ∑ j, a j i * x.2 j := fun i => by
      have := h2 i
      rw [hei] at this
      simp only [di] at this
      rw [dotProduct] at this
      linarith
    refine ⟨x.1, x.1.2, fun γ hγ => ?_⟩
    have hγ' := aux_mem_poly.1 hγ
    have e1 : (b₀ + ∑ i, γ i • B i) ⬝ᵥ (x.1 : Fin N → ℝ) =
        b₀ ⬝ᵥ (x.1 : Fin N → ℝ) + ∑ j, x.2 j * (a j ⬝ᵥ γ) := by
      rw [add_dotProduct, aux_sum_smul_dot]
      congr 1
      simp only [he]
      simp only [Finset.mul_sum, dotProduct]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ j, x.2 j * (a j ⬝ᵥ γ) ≤ β ⬝ᵥ x.2 := by
      rw [dotProduct]
      exact Finset.sum_le_sum fun j _ => by
        rw [mul_comm (β j)]
        exact mul_le_mul_of_nonneg_left (hγ' j) (hs j)
    rw [e1]
    linarith
  · obtain ⟨y, z, hy, hsum, hneg⟩ := (LP.farkas ai bi ei di).1 hfeas
    have hy' : ∀ o, 0 ≤ y o := hy
    have hc : 0 < y none := by
      have : y ⬝ᵥ bi + z ⬝ᵥ di = - y none := by
        simp [dotProduct, Fintype.sum_option, bi, di]
      linarith
    have hev := fun x => LinearMap.congr_fun hsum x
    have hv : ∀ v ∈ V, y none * (b₀ ⬝ᵥ v) = ∑ i, z i * (B i ⬝ᵥ v) := by
      intro v hv
      have := hev (⟨v, hv⟩, 0)
      simp only [LinearMap.add_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply, Fintype.sum_option, hai_none,
        hai_some, hei] at this
      simp at this
      linarith
    have hj : ∀ j, y none * β j - y (some j) + ∑ i, z i * a j i = 0 := by
      intro j
      have := hev (0, Pi.single j 1)
      simp only [LinearMap.add_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply, Fintype.sum_option, hai_none,
        hai_some, hei] at this
      simp [dotProduct_single, Pi.single_apply] at this
      linarith
    have hγP : (fun i => -z i / y none) ∈ poly a β := by
      rw [aux_mem_poly]
      intro j
      have e : a j ⬝ᵥ (fun i => -z i / y none) = -(∑ i, z i * a j i) / y none := by
        rw [eq_div_iff hc.ne']
        simp only [dotProduct, Finset.sum_mul]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, div_mul_cancel₀ _ hc.ne']
        ring
      rw [e, div_le_iff₀ hc]
      have := hj j
      linarith [hy' (some j)]
    obtain ⟨v, hvV, hv0⟩ := h _ hγP
    refine absurd ?_ hv0
    rw [add_dotProduct, aux_sum_smul_dot]
    have e : ∑ i, -z i / y none * (B i ⬝ᵥ v) = -(∑ i, z i * (B i ⬝ᵥ v)) / y none := by
      rw [eq_div_iff hc.ne']
      simp only [Finset.sum_mul]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_right_comm, div_mul_cancel₀ _ hc.ne']
      ring
    rw [e, ← hv v hvV, neg_div, mul_div_cancel_left₀ _ hc.ne']
    ring

theorem isExtreme_argmaxOn {n : ℕ} (S : Set (Fin n → ℝ)) (u : Fin n → ℝ) :
    IsExtreme ℝ S (argmaxOn S u) := by
  refine ⟨fun x hx => hx.1, ?_⟩
  intro x₁ h1 x₂ h2 x hx hseg
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hseg
  rw [aux_mem_argmaxOn] at hx
  have k1 := hx.2 x₁ h1
  have k2 := hx.2 x₂ h2
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at k1 k2 hx
  obtain ⟨e1, e2⟩ := aux_seg ht hs hst k1 k2
  refine aux_mem_argmaxOn.2 ⟨h1, fun y hy => ?_⟩
  have := hx.2 y hy
  linarith

theorem kkt_of_posDef {N m : ℕ} (A₀ : Matrix (Fin N) (Fin N) ℝ)
    (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (hA : ∀ i, (A i).IsSymm)
    (I : Fin m → Prop) (u γh : Fin m → ℝ) (hγI : ∀ i, I i → 0 ≤ γh i)
    (hPD : (A₀ + ∑ i, γh i • A i).PosDef)
    (hmax : ∀ γ : Fin m → ℝ, (A₀ + ∑ i, γ i • A i).PosSemidef → (∀ i, I i → 0 ≤ γ i) →
      u ⬝ᵥ γ ≤ u ⬝ᵥ γh) :
    ∀ i, (I i → u i ≤ 0) ∧ (¬ I i → u i = 0) ∧ γh i * u i = 0 := by
  classical
  intro i
  have hsym : (A₀ + ∑ j, γh j • A j).IsSymm := by
    have := hPD.isHermitian
    unfold Matrix.IsHermitian at this
    rw [conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hint := Matrix.PosDef.mem_interior_psdForm hPD
  have hev : ∀ᶠ ε in nhds (0:ℝ), (A₀ + ∑ j, γh j • A j) + ε • A i ∈
      (psdForm (Fin N) : Set (Matrix (Fin N) (Fin N) ℝ)) := by
    have ht : Filter.Tendsto (fun ε : ℝ => (A₀ + ∑ j, γh j • A j) + ε • A i) (nhds 0)
        (nhds (A₀ + ∑ j, γh j • A j)) := by
      have hc : Continuous (fun ε : ℝ => (A₀ + ∑ j, γh j • A j) + ε • A i) := by fun_prop
      simpa using hc.tendsto 0
    exact ht.eventually (mem_interior_iff_mem_nhds.1 hint)
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 hev
  have step : ∀ ε : ℝ, |ε| < δ → (∀ j, I j → 0 ≤ ((γh + Pi.single i ε : Fin m → ℝ)) j) → ε * u i ≤ 0 := by
    intro ε hε hI'
    have hG : A₀ + ∑ j, ((γh + Pi.single i ε : Fin m → ℝ)) j • A j = (A₀ + ∑ j, γh j • A j) + ε • A i := by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, aux_sum_single_smul, add_assoc]
    have hpsd : (A₀ + ∑ j, ((γh + Pi.single i ε : Fin m → ℝ)) j • A j).PosSemidef := by
      rw [hG]
      exact (mem_psdForm_iff_posSemidef (hsym.add ((hA i).smul ε))).1
        (hδP (show dist ε 0 < δ by rwa [Real.dist_eq, sub_zero]))
    have := hmax _ hpsd hI'
    rw [dotProduct_add, dotProduct_single] at this
    linarith [mul_comm (u i) ε]
  have hhalf : |δ / 2| < δ := by
    rw [abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ
  have hup : u i ≤ 0 := by
    have := step (δ / 2) hhalf (fun j hj => by
      simp only [Pi.add_apply]
      by_cases hji : j = i
      · rw [hji, Pi.single_eq_same]
        have := hγI i (hji ▸ hj)
        linarith
      · rw [Pi.single_eq_of_ne hji, add_zero]
        exact hγI j hj)
    by_contra h
    push Not at h
    have := mul_pos (half_pos hδ) h
    linarith
  by_cases hI : I i
  · refine ⟨fun _ => hup, fun h => absurd hI h, ?_⟩
    rcases (hγI i hI).lt_or_eq with hpos' | hzero
    · obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = -min (δ / 2) (γh i) := ⟨_, rfl⟩
      have hmpos : 0 < min (δ / 2) (γh i) := lt_min (half_pos hδ) hpos'
      have hε : |ε| < δ := by
        rw [hεdef, abs_neg, abs_of_pos hmpos]
        exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
      have hs : ∀ j, I j → 0 ≤ ((γh + Pi.single i ε : Fin m → ℝ)) j := by
        intro j hj
        simp only [Pi.add_apply]
        by_cases hji : j = i
        · rw [hji, Pi.single_eq_same, hεdef]
          have := min_le_right (δ / 2) (γh i)
          linarith
        · rw [Pi.single_eq_of_ne hji, add_zero]
          exact hγI j hj
      have h1 := step ε hε hs
      have hεneg : ε < 0 := by rw [hεdef]; exact neg_neg_of_pos hmpos
      have hge : 0 ≤ u i := by
        by_contra h
        push Not at h
        have := mul_pos_of_neg_of_neg hεneg h
        linarith
      rw [le_antisymm hup hge, mul_zero]
    · rw [← hzero, zero_mul]
  · have hs : ∀ ε : ℝ, ∀ j, I j → 0 ≤ ((γh + Pi.single i ε : Fin m → ℝ)) j := by
      intro ε j hj
      have hji : j ≠ i := fun h => hI (h ▸ hj)
      simp only [Pi.add_apply]
      rw [Pi.single_eq_of_ne hji, add_zero]
      exact hγI j hj
    have h1 := step (-(δ / 2)) (by rw [abs_neg]; exact hhalf) (hs _)
    have hge : 0 ≤ u i := by
      by_contra h
      push Not at h
      have := mul_pos_of_neg_of_neg (neg_neg_of_pos (half_pos hδ)) h
      linarith
    have hu : u i = 0 := le_antisymm hup hge
    exact ⟨fun h => absurd h hI, fun _ => hu, by rw [hu, mul_zero]⟩

end

section
open Matrix

namespace RankRedKit

theorem mem_shorFeasible_vecMulVec {N m : ℕ} (A : Fin m → Matrix (Fin N) (Fin N) ℝ)
    (b : Fin m → Fin N → ℝ) (c : Fin m → ℝ) (I : Fin m → Prop) (x : Fin N → ℝ)
    (hx : ∀ i, (I i → quad (A i) (b i) (c i) x ≤ 0) ∧ (¬ I i → quad (A i) (b i) (c i) x = 0)) :
    (x, vecMulVec x x) ∈ shorFeasible A b c I := by
  refine ⟨aux_vecMulVec_isSymm x, ?_, fun i => ?_⟩
  · rw [liftY_posSemidef_iff, sub_self]; exact PosSemidef.zero
  · simp only [trace_liftQ_mul_liftY, sub_self, Matrix.mul_zero, trace_zero, add_zero]
    exact hx i

end RankRedKit

end

noncomputable section
open Matrix QCQPTightness.Exact

theorem lift_mem {N m : ℕ} (P : QCQP N m) {x : Fin N → ℝ} (hx : x ∈ P.feasible) :
    (x, vecMulVec x x) ∈ P.sdpFeasible ∧ (QCQPTightness.ConvHull.liftQ P.A₀ P.b₀ P.c₀ *
      QCQPTightness.ConvHull.liftY x (vecMulVec x x)).trace = P.q₀ x := by
  refine ⟨RankRedKit.mem_shorFeasible_vecMulVec P.A P.b P.c P.IsIneq x hx, ?_⟩
  have := trace_eq P.A₀ P.b₀ P.c₀ x (vecMulVec x x)
  rw [sub_self, Matrix.mul_zero, Matrix.trace_zero, add_zero] at this
  exact this

theorem optSDP_le_trace {N m : ℕ} (P : QCQP N m) {x : Fin N → ℝ} {X : Matrix (Fin N) (Fin N) ℝ}
    (hX : (x, X) ∈ P.sdpFeasible) :
    P.OptSDP ≤ (((QCQPTightness.ConvHull.liftQ P.A₀ P.b₀ P.c₀ *
      QCQPTightness.ConvHull.liftY x X).trace : ℝ) : EReal) :=
  iInf₂_le (f := fun (p : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ) (_ : p ∈ P.sdpFeasible) =>
    (((QCQPTightness.ConvHull.liftQ P.A₀ P.b₀ P.c₀ *
      QCQPTightness.ConvHull.liftY p.1 p.2).trace : ℝ) : EReal)) (x, X) hX

end

noncomputable section
open Matrix

theorem starProjection_map_eq_zero_iff {N : ℕ} (V : Submodule ℝ (Fin N → ℝ))
    (b : Fin N → ℝ) :
    (V.map (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.toLinearMap).starProjection
        (WithLp.toLp 2 b) = 0 ↔ ∀ v ∈ V, b ⬝ᵥ v = 0 := by
  rw [Submodule.starProjection_apply, Submodule.coe_eq_zero,
    Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.mem_orthogonal]
  constructor
  · intro h v hv
    have := h _ (Submodule.mem_map_of_mem hv)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simpa using this
  · intro h u hu
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa using h v hv

end

noncomputable section
open Matrix QCQPTightness.Exact

theorem part1 {N m : ℕ} (P : QCQP N m) (h1 : P.Assumption1) (h3 : P.Assumption3)
    (hproj : ∀ F, P.IsSemidefiniteFace F → (0 : EuclideanSpace ℝ (Fin N)) ∉ projB P F) :
    ∀ p ∈ P.DSDP, (∀ p' ∈ P.DSDP, 2 * p.2 ≤ 2 * p'.2) → p ∈ P.D := by
  rintro ⟨x, t⟩ hp hmin
  obtain ⟨_, γs, hγs, hPD⟩ := h1
  have hT := dsdp_iff P γs hγs hPD
  have hb := (hT x t).1 hp
  obtain ⟨p, a, β, hΓ0⟩ := h3
  have hΓ : P.Gamma = poly a β := hΓ0
  set u : Fin m → ℝ := fun i => P.q i x with hu
  have hface : P.faceOf x = argmaxOn (poly a β) u := by
    ext γ
    simp only [QCQP.faceOf, argmaxOn, Set.mem_setOf_eq, ← hΓ, qγ_eq,
      add_le_add_iff_left]
    exact Iff.rfl
  have hγsΓ : γs ∈ P.Gamma := ⟨hPD.posSemidef, hγs⟩
  have hne : (argmaxOn (poly a β) u).Nonempty := by
    refine argmaxOn_nonempty a β u ⟨γs, by rw [← hΓ]; exact hγsΓ⟩
      ⟨2 * t - P.q₀ x, ?_⟩
    rintro _ ⟨γ, hγ, rfl⟩
    have := hb γ (by rw [hΓ]; exact hγ)
    rw [qγ_eq] at this
    show u ⬝ᵥ γ ≤ 2 * t - P.q₀ x
    linarith
  obtain ⟨γh, hγh⟩ := hne
  have hγhF : γh ∈ P.faceOf x := by rw [hface]; exact hγh
  by_cases hdef : ∃ γ ∈ P.faceOf x, (P.Aγ γ).PosDef
  · obtain ⟨γd, hγd, hPDd⟩ := hdef
    have hγdΓ : γd ∈ P.Gamma := hγd.1
    rw [hface] at hγd
    have hkkt := kkt_of_posDef P.A₀ P.A P.A_symm P.IsIneq u γd hγdΓ.2 hPDd
      (fun γ h1 h2 => hγd.2 γ (by rw [← hΓ]; exact ⟨h1, h2⟩))
    refine ⟨?_, fun i => ⟨(hkkt i).1, (hkkt i).2.1⟩⟩
    have hq := hb γd hγdΓ
    have hz : ∑ i, γd i * P.q i x = 0 := Finset.sum_eq_zero fun i _ => (hkkt i).2.2
    simp only [QCQP.qγ, hz, add_zero] at hq
    exact hq
  · have hsemi : P.IsSemidefiniteFace (P.faceOf x) := by
      refine ⟨⟨⟨γh, hγhF⟩, ?_, ?_⟩, hdef⟩
      · rw [hface]; exact convex_argmaxOn (convex_poly a β) u
      · rw [hface, hΓ]; exact isExtreme_argmaxOn _ u
    have h0 := hproj _ hsemi
    obtain ⟨p', a', β', hpoly⟩ := argmaxOn_poly_isPoly a β u
    have hnz : ∀ γ ∈ poly a' β', ∃ v ∈ P.V (P.faceOf x),
        (P.b₀ + ∑ i, γ i • P.b i) ⬝ᵥ v ≠ 0 := by
      intro γ hγ
      by_contra hcon
      push_neg at hcon
      apply h0
      refine ⟨γ, ?_, ?_⟩
      · rw [hface, hpoly]; exact hγ
      · exact (starProjection_map_eq_zero_iff (P.V (P.faceOf x)) (P.bγ γ)).2 hcon
    obtain ⟨v, hvV, hv⟩ := exists_dotProduct_le_neg_one a' β' P.b₀ P.b _ hnz
    have hker : ∀ γ ∈ argmaxOn (poly a β) u, P.Aγ γ *ᵥ v = 0 := by
      intro γ hγ
      rw [← hface] at hγ
      have := hvV
      simp only [QCQP.V, Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
      exact this γ hγ
    have hbv : ∀ γ ∈ argmaxOn (poly a β) u, P.bγ γ ⬝ᵥ v ≤ -1 := by
      intro γ hγ
      rw [hpoly] at hγ
      exact hv γ hγ
    obtain ⟨α, hα, hdesc⟩ := descent P a β hΓ x v γh hγh hker hbv
    have hmem : (x + α • v, (P.qγ γh x - 2 * α) / 2) ∈ P.DSDP :=
      (hT _ _).2 fun γ hγ => by have := hdesc γ hγ; linarith
    have h5 := hmin _ hmem
    have h6 := hb γh hγhF.1
    dsimp only at h5
    exfalso
    linarith

end

section
open Matrix

namespace RankRedKit

theorem shor_exists_isMinOn {N m : ℕ} (A₀ : Matrix (Fin N) (Fin N) ℝ) (b₀ : Fin N → ℝ) (c₀ : ℝ)
    (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (b : Fin m → Fin N → ℝ) (c : Fin m → ℝ)
    (I : Fin m → Prop) (γ : Fin m → ℝ) (hγ : ∀ i, I i → 0 ≤ γ i)
    (hPD : (A₀ + ∑ i, γ i • A i).PosDef) (hne : (shorFeasible A b c I).Nonempty) :
    ∃ p ∈ shorFeasible A b c I, ∀ p' ∈ shorFeasible A b c I,
      (liftQ A₀ b₀ c₀ * liftY p.1 p.2).trace ≤ (liftQ A₀ b₀ c₀ * liftY p'.1 p'.2).trace := by
  classical
  let f : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ → ℝ :=
    fun p => (liftQ A₀ b₀ c₀ * liftY p.1 p.2).trace
  have hfc : Continuous f := (continuous_const.matrix_mul aux_continuous_liftY).matrix_trace
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨l, hl0, hl⟩ := aux_posDef_coercive hPD
  have hlow : ∀ p ∈ shorFeasible A b c I,
      quad (A₀ + ∑ i, γ i • A i) (b₀ + ∑ i, γ i • b i) (c₀ + ∑ i, γ i * c i) p.1 +
        ((A₀ + ∑ i, γ i • A i) * (p.2 - vecMulVec p.1 p.1)).trace ≤ f p := by
    rintro ⟨x, X⟩ ⟨-, -, hC⟩
    rw [← trace_liftQ_mul_liftY, aux_liftQ_comb, Matrix.add_mul, trace_add, Finset.sum_mul,
      trace_sum]
    have hi : ∀ i, (γ i • liftQ (A i) (b i) (c i) * liftY x X).trace ≤ 0 := by
      intro i
      rw [Matrix.smul_mul, trace_smul, smul_eq_mul]
      by_cases hi : I i
      · exact mul_nonpos_of_nonneg_of_nonpos (hγ i hi) ((hC i).1 hi)
      · rw [(hC i).2 hi, mul_zero]
    have := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hi i
    show _ ≤ (liftQ A₀ b₀ c₀ * liftY x X).trace
    linarith
  have hbound : ∀ p ∈ shorFeasible A b c I, f p ≤ f p₀ →
      (∀ i, |p.1 i| ≤ 1 + 2 * ((2 * l * f p₀ + 4 * ((b₀ + ∑ i, γ i • b i) ⬝ᵥ (b₀ + ∑ i, γ i • b i))
        - 2 * l * (c₀ + ∑ i, γ i * c i)) / l ^ 2)) ∧
      (∀ i j, |p.2 i j| ≤ 1 + 2 * ((2 * l * f p₀ + 4 * ((b₀ + ∑ i, γ i • b i) ⬝ᵥ
        (b₀ + ∑ i, γ i • b i)) - 2 * l * (c₀ + ∑ i, γ i * c i)) / l ^ 2)) := by
    rintro ⟨x, X⟩ hp hfp
    have hW : (X - vecMulVec x x).PosSemidef := (liftY_posSemidef_iff x X).mp hp.2.1
    have h1 := hlow _ hp
    dsimp only at h1
    unfold quad at h1
    have hF : x ⬝ᵥ ((A₀ + ∑ i, γ i • A i) *ᵥ x) + 2 * ((b₀ + ∑ i, γ i • b i) ⬝ᵥ x) +
        (c₀ + ∑ i, γ i * c i) + ((A₀ + ∑ i, γ i • A i) * (X - vecMulVec x x)).trace ≤ f p₀ := by
      linarith
    obtain ⟨hax, htx⟩ := aux_coercive_num hl0 (hl x) (aux_trace_lower hl hW)
      (aux_sq_expand l x (b₀ + ∑ i, γ i • b i)) hF hW.trace_nonneg (aux_dot_self_nonneg x)
    have ha0 := aux_dot_self_nonneg x
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · have := aux_sq_le_dot x i
      show |x i| ≤ _
      nlinarith [abs_mul_abs_self (x i), abs_nonneg (x i), sq_nonneg (|x i| - 1)]
    · have hWij := aux_psd_entry hW i j
      have hX : X i j = (X - vecMulVec x x) i j + x i * x j := by
        simp [vecMulVec_apply]
      have hxi := aux_sq_le_dot x i
      have hxj := aux_sq_le_dot x j
      have hxx : |x i * x j| ≤ x ⬝ᵥ x := by
        rw [abs_mul]
        nlinarith [abs_mul_abs_self (x i), abs_mul_abs_self (x j), sq_nonneg (|x i| - |x j|)]
      show |X i j| ≤ _
      rw [hX]
      have := abs_add_le ((X - vecMulVec x x) i j) (x i * x j)
      linarith
  have hKc : IsCompact (shorFeasible A b c I ∩ {p | f p ≤ f p₀}) := by
    set R := 1 + 2 * ((2 * l * f p₀ + 4 * ((b₀ + ∑ i, γ i • b i) ⬝ᵥ (b₀ + ∑ i, γ i • b i))
        - 2 * l * (c₀ + ∑ i, γ i * c i)) / l ^ 2) with hR
    have hT : IsCompact ((Set.univ.pi fun _ : Fin N => Set.Icc (-R) R) ×ˢ
        (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => Set.Icc (-R) R) :
          Set ((Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ)) :=
      (isCompact_univ_pi fun _ => isCompact_Icc).prod
        (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)
    refine hT.of_isClosed_subset
      ((aux_isClosed_shorFeasible A b c I).inter (isClosed_le hfc continuous_const)) ?_
    rintro p ⟨hp, hfp⟩
    obtain ⟨h1, h2⟩ := hbound p hp hfp
    exact ⟨fun i _ => abs_le.mp (h1 i), fun i _ j _ => abs_le.mp (h2 i j)⟩
  obtain ⟨p, ⟨hpS, hpM⟩, hmin⟩ := hKc.exists_isMinOn ⟨p₀, hp₀, (le_refl (f p₀) : f p₀ ≤ f p₀)⟩ hfc.continuousOn
  refine ⟨p, hpS, fun p' hp' => ?_⟩
  show f p ≤ f p'
  by_cases h : f p' ≤ f p₀
  · exact isMinOn_iff.mp hmin p' ⟨hp', h⟩
  · exact le_trans hpM (le_of_not_ge h)

end RankRedKit

end

noncomputable section
open Matrix QCQPTightness.Exact

theorem part2 {N m : ℕ} (P : QCQP N m) (h1 : P.Assumption1)
    (hD : ∀ p ∈ P.DSDP, (∀ p' ∈ P.DSDP, 2 * p.2 ≤ 2 * p'.2) → p ∈ P.D) :
    P.Opt = P.OptSDP := by
  apply le_antisymm
  · obtain ⟨⟨x₀, hx₀⟩, γ, hγ, hPD⟩ := h1
    obtain ⟨p, hp, hmin⟩ := RankRedKit.shor_exists_isMinOn P.A₀ P.b₀ P.c₀ P.A P.b P.c P.IsIneq
      γ hγ hPD ⟨_, (lift_mem P hx₀).1⟩
    set f := (QCQPTightness.ConvHull.liftQ P.A₀ P.b₀ P.c₀ *
        QCQPTightness.ConvHull.liftY p.1 p.2).trace with hf
    have hopt : P.OptSDP = ((f : ℝ) : EReal) := by
      refine le_antisymm (optSDP_le_trace (x := p.1) (X := p.2) P hp) ?_
      unfold QCQP.OptSDP
      exact le_iInf₂ fun q hq => EReal.coe_le_coe_iff.2 (hmin q hq)
    have hmem : (p.1, f / 2) ∈ P.DSDP := ⟨p.2, hp, by show f ≤ 2 * (f / 2); linarith⟩
    have hDp := hD _ hmem (by
      rintro ⟨x', t'⟩ ⟨X', hX', hle⟩
      have := hmin _ hX'
      show 2 * (f / 2) ≤ 2 * t'
      have h2 : f ≤ (QCQPTightness.ConvHull.liftQ P.A₀ P.b₀ P.c₀ *
          QCQPTightness.ConvHull.liftY x' X').trace := this
      linarith)
    obtain ⟨hq, hx⟩ := hDp
    calc P.Opt ≤ ((P.q₀ p.1 : ℝ) : EReal) := by
          unfold QCQP.Opt
          exact iInf₂_le (f := fun y (_ : y ∈ P.feasible) => ((P.q₀ y : ℝ) : EReal)) p.1 hx
      _ ≤ ((f : ℝ) : EReal) := EReal.coe_le_coe_iff.2 (by
          have : P.q₀ p.1 ≤ 2 * (f / 2) := hq
          linarith)
      _ = P.OptSDP := hopt.symm
  · unfold QCQP.Opt
    refine le_iInf₂ fun x hx => ?_
    obtain ⟨hm, he⟩ := lift_mem P hx
    rw [← he]
    exact optSDP_le_trace P hm

end

noncomputable section

open QCQPTightness.Exact in
theorem solution {N m : ℕ} (P : QCQP N m) (hm : 1 ≤ m) (h1 : P.Assumption1)
    (h3 : P.Assumption3)
    (hproj : ∀ F, P.IsSemidefiniteFace F → (0 : EuclideanSpace ℝ (Fin N)) ∉ projB P F) :
    (∀ p ∈ P.DSDP, (∀ p' ∈ P.DSDP, 2 * p.2 ≤ 2 * p'.2) → p ∈ P.D) ∧ P.Opt = P.OptSDP :=
  ⟨part1 P h1 h3 hproj,
    part2 P h1
      (part1 P h1 h3 hproj)⟩

end
