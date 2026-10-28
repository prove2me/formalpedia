-- Prove2me | solution 2 for SDDiP.Envelope.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T06:02:20.342979+00:00
-- url     : https://prove2.me/submissions/e4a110fd-e89d-448b-aa96-d61f48bb9318

import Mathlib
import Definitions.Def_SDDiP_Envelope_ConvexLowerEnvelope
import Theorems.Thm_LP_farkas

-- carved verbatim out of submission c6ce6ea4-4322-4a29-8789-deebf63433e8, lines 3149-3225

section
open SDDiP.Envelope Matrix

abbrev E (n : ℕ) := (Fin n → ℝ) × ℝ

end

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

section
open SDDiP.Envelope Matrix

def afun {n : ℕ} (v : Fin n → ℝ) : Module.Dual ℝ (E n) where
  toFun p := p.1 ⬝ᵥ v + p.2
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct]; ring
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, RingHom.id_apply]
    ring

def vb {n : ℕ} (b : Fin n → Bool) : Fin n → ℝ := fun i => if b i then 1 else 0

def P {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Set (E n) := {p | ∀ b, afun (vb b) p ≤ f (vb b)}

lemma afun_apply {n : ℕ} (v : Fin n → ℝ) (p : E n) : afun v p = p.1 ⬝ᵥ v + p.2 := rfl

lemma afun_comb {n : ℕ} (x x' : Fin n → ℝ) (p : E n) (a b : ℝ) (hab : a + b = 1) :
    afun (a • x + b • x') p = a * afun x p + b * afun x' p := by
  simp only [afun_apply, dotProduct_add, dotProduct_smul, smul_eq_mul]
  linear_combination (-p.2) * hab

lemma cube_convex (n : ℕ) : Convex ℝ (cube n) := convex_Icc _ _

lemma affine_convex {n : ℕ} (p : E n) : ConvexOn ℝ (cube n) (fun z => afun z p) :=
  ⟨cube_convex n, fun x _ x' _ a b _ _ hab => le_of_eq (by
    simp only [smul_eq_mul]; exact afun_comb x x' p a b hab)⟩

lemma eq_vb {n : ℕ} {v : Fin n → ℝ} (hv : v ∈ binaryPoints n) :
    v = vb (fun i => decide (v i = 1)) := by
  funext i
  unfold vb
  rcases hv i with h | h <;> simp [h]

lemma hull_eq (n : ℕ) : convexHull ℝ (binaryPoints n) = cube n := by
  have h1 : binaryPoints n = Set.univ.pi (fun _ : Fin n => ({0, 1} : Set ℝ)) := by
    ext x; simp [binaryPoints, Set.mem_pi]
  rw [h1, convexHull_pi, convexHull_pair, segment_eq_Icc zero_le_one]
  ext x
  simp [cube, Set.mem_pi, Pi.le_def, forall_and]

lemma affine_under {n : ℕ} {f : (Fin n → ℝ) → ℝ} {p : E n} (hp : p ∈ P f) :
    IsConvexUnderestimator (binaryPoints n) f (fun z => afun z p) := by
  refine ⟨by rw [hull_eq]; exact affine_convex p, fun v hv => ?_⟩
  rw [eq_vb hv]
  exact hp _

end

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def aux1_T (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) :
    (ι → ℝ) × (κ → ℝ) →ₗ[ℝ] Module.Dual ℝ E where
  toFun yz := ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
      ← Finset.smul_sum, smul_add, RingHom.id_apply]

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

end

section
open SDDiP.Envelope Matrix

lemma eval {n : ℕ} {x : Fin n → ℝ} (y : (Fin n → Bool) → ℝ) (h1 : ∑ b, y b = 1)
    (hx : ∑ b, y b • vb b = x) (p : E n) :
    afun x p = ∑ b, y b * afun (vb b) p := by
  rw [afun_apply, ← hx, dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul, afun_apply, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, h1, one_mul]

end

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

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

end

section
open SDDiP.Envelope Matrix

lemma descent {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → V →ₗ[ℝ] ℝ) (r : ι → ℝ) (hpt : ∀ d, (∀ i, a i d = 0) → d = 0) :
    ∀ (N : ℕ) (p : V), (∀ i, a i p ≤ r i) →
      (Finset.univ.filter fun i => a i p < r i).card = N →
      ∃ p', (∀ i, a i p' ≤ r i) ∧ (∀ i, a i p = r i → a i p' = r i) ∧
        ∀ q, (∀ i, a i p' = r i → a i q = r i) → q = p' := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro p hp hN
  by_cases huniq : ∀ q, (∀ i, a i p = r i → a i q = r i) → q = p
  · exact ⟨p, hp, fun i h => h, huniq⟩
  push Not at huniq
  obtain ⟨q, hq, hqp⟩ := huniq
  have hd0 : ∀ i, a i p = r i → a i (q - p) = 0 := fun i hi => by
    rw [map_sub, hq i hi, hi, sub_self]
  obtain ⟨j, hj⟩ : ∃ j, a j (q - p) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hqp (sub_eq_zero.mp (hpt _ hc))
  obtain ⟨d', hd'0, hj'⟩ : ∃ d' : V, (∀ i, a i p = r i → a i d' = 0) ∧ 0 < a j d' := by
    rcases lt_or_gt_of_ne hj with h | h
    · exact ⟨-(q - p), fun i hi => by rw [map_neg, hd0 i hi, neg_zero], by
        rw [map_neg]; linarith⟩
    · exact ⟨q - p, hd0, h⟩
  let S := Finset.univ.filter fun i => 0 < a i d'
  have hS : S.Nonempty := ⟨j, by simp [S, hj']⟩
  obtain ⟨i0, hi0S, hi0min⟩ := S.exists_min_image (fun i => (r i - a i p) / a i d') hS
  have hi0pos : 0 < a i0 d' := (Finset.mem_filter.mp hi0S).2
  obtain ⟨t, ht⟩ : ∃ t, t = (r i0 - a i0 p) / a i0 d' := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := ht ▸ div_nonneg (by linarith [hp i0]) hi0pos.le
  have hval : ∀ i, a i (p + t • d') = a i p + t * a i d' := fun i => by
    rw [map_add, map_smul, smul_eq_mul]
  have hp'' : ∀ i, a i (p + t • d') ≤ r i := by
    intro i
    rw [hval]
    by_cases hi : 0 < a i d'
    · have h1 : t ≤ (r i - a i p) / a i d' := ht ▸ hi0min i (by simp [S, hi])
      have h2 := (le_div_iff₀ hi).mp h1
      linarith
    · push Not at hi
      have := mul_nonpos_of_nonneg_of_nonpos ht0 hi
      linarith [hp i]
  have htight : ∀ i, a i p = r i → a i (p + t • d') = r i := fun i hi => by
    rw [hval, hd'0 i hi, hi]; ring
  have htm : t * a i0 d' = r i0 - a i0 p := by rw [ht]; exact div_mul_cancel₀ _ hi0pos.ne'
  have hi0t : a i0 (p + t • d') = r i0 := by rw [hval]; linarith
  have hi0nt : a i0 p < r i0 := by
    rcases (hp i0).lt_or_eq with h | h
    · exact h
    · exact absurd (hd'0 i0 h) hi0pos.ne'
  have hcard : (Finset.univ.filter fun i => a i (p + t • d') < r i).card < N := by
    rw [← hN]
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_contra hc
      push Not at hc
      have := htight i (le_antisymm (hp i) hc)
      linarith
    · intro hsub
      have := hsub (by simp [hi0nt] : i0 ∈ Finset.univ.filter fun i => a i p < r i)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      linarith
  obtain ⟨p', h1, h2, h3⟩ := ih _ hcard (p + t • d') hp'' rfl
  exact ⟨p', h1, fun i hi => h2 i (htight i hi), h3⟩

noncomputable def env {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup ((fun p => afun x p) '' P f)

end

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

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

section
open SDDiP.Envelope Matrix

lemma regroup {ι β M : Type*} [Fintype ι] [Fintype β] [DecidableEq β] [AddCommMonoid M]
    [Module ℝ M] (w : ι → ℝ) (bz : ι → β) (G : β → M) :
    ∑ b, (∑ i, if bz i = b then w i else 0) • G b = ∑ i, w i • G (bz i) := by
  simp only [Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

lemma weights {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ cube n) :
    ∃ y : (Fin n → Bool) → ℝ, (∀ b, 0 ≤ y b) ∧ ∑ b, y b = 1 ∧ ∑ b, y b • vb b = x := by
  rw [← hull_eq] at hx
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hx⟩ := mem_convexHull_iff_exists_fintype.mp hx
  let bz : ι → Fin n → Bool := fun i j => decide (z i j = 1)
  have hbz : ∀ i, vb (bz i) = z i := fun i => (eq_vb (hz i)).symm
  refine ⟨fun b => ∑ i, if bz i = b then w i else 0, fun b => Finset.sum_nonneg fun i _ => ?_,
    ?_, ?_⟩
  · split_ifs
    · exact hw0 i
    · exact le_rfl
  · have := regroup w bz (fun _ => (1 : ℝ))
    simp only [smul_eq_mul, mul_one] at this
    rw [this, hw1]
  · rw [regroup w bz vb]
    simp only [hbz]
    exact hx

lemma key {n : ℕ} (f : (Fin n → ℝ) → ℝ) {x : Fin n → ℝ} (hx : x ∈ cube n) :
    ∃ p ∈ P f, ∃ y : (Fin n → Bool) → ℝ, (∀ b, 0 ≤ y b) ∧ ∑ b, y b = 1 ∧
      ∑ b, y b • vb b = x ∧ afun x p = ∑ b, y b * f (vb b) := by
  obtain ⟨y0, hy0, hy01, hy0x⟩ := weights hx
  let a : (Fin n → Bool) → Module.Dual ℝ (E n) := fun b => afun (vb b)
  let bb : (Fin n → Bool) → ℝ := fun b => f (vb b)
  let e : Empty → Module.Dual ℝ (E n) := fun k => k.elim
  let d : Empty → ℝ := fun k => k.elim
  have hP : (LP.Feas a bb e d).Nonempty := by
    refine ⟨(0, -∑ b, |f (vb b)|), fun b => ?_, fun k => k.elim⟩
    show (0 : Fin n → ℝ) ⬝ᵥ vb b + -∑ b, |f (vb b)| ≤ f (vb b)
    have := Finset.single_le_sum (f := fun b => |f (vb b)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ b)
    rw [zero_dotProduct]
    linarith [neg_abs_le (f (vb b))]
  have hD : (LP.DualFeas a e (afun x)).Nonempty := by
    refine ⟨(y0, fun k => k.elim), fun b => hy0 b, ?_⟩
    apply LinearMap.ext
    intro p
    rw [Fintype.sum_empty (ι := Empty), add_zero, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul, a]
    exact (eval y0 hy01 hy0x p).symm
  obtain ⟨v, ⟨⟨p, hp, hpv⟩, -⟩, ⟨⟨yz, hyz, hyzv⟩, -⟩⟩ :=
    LP.strong_duality a bb e d (afun x) hP hD
  obtain ⟨hy, hsum⟩ := hyz
  have hev : ∀ q : E n, ∑ b, yz.1 b * afun (vb b) q = afun x q := by
    intro q
    have := congrArg (fun φ : Module.Dual ℝ (E n) => φ q) hsum
    simp only [Fintype.sum_empty (ι := Empty), add_zero, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, a] at this
    exact this
  have h1 : ∑ b, yz.1 b = 1 := by
    have := hev (0, 1)
    simpa [afun_apply] using this
  have hx' : ∑ b, yz.1 b • vb b = x := by
    funext j
    have := hev (Pi.single j 1, 0)
    simp only [afun_apply, single_dotProduct, one_mul, add_zero] at this
    rw [Finset.sum_apply]
    simpa [Pi.smul_apply, smul_eq_mul] using this
  refine ⟨p, hp.1, yz.1, hy, h1, hx', ?_⟩
  have hd0 : yz.2 ⬝ᵥ d = 0 := by simp [dotProduct, Finset.univ_eq_empty]
  simp only at hyzv
  rw [hd0, add_zero] at hyzv
  rw [hpv, ← hyzv]
  rfl

lemma weak {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (y : (Fin n → Bool) → ℝ)
    (hy : ∀ b, 0 ≤ y b) (h1 : ∑ b, y b = 1) (hx : ∑ b, y b • vb b = x) {q : E n}
    (hq : q ∈ P f) : afun x q ≤ ∑ b, y b * f (vb b) := by
  rw [eval y h1 hx q]
  exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hq b) (hy b)

lemma env_spec {n : ℕ} (f : (Fin n → ℝ) → ℝ) {x : Fin n → ℝ} (hx : x ∈ cube n) :
    ∃ p ∈ P f, env f x = afun x p ∧ (∀ q ∈ P f, afun x q ≤ env f x) ∧
      ∃ y : (Fin n → Bool) → ℝ, (∀ b, 0 ≤ y b) ∧ ∑ b, y b = 1 ∧
        ∑ b, y b • vb b = x ∧ env f x = ∑ b, y b * f (vb b) := by
  obtain ⟨p, hp, y, hy, h1, hxy, hpv⟩ := key f hx
  have hG : IsGreatest ((fun p => afun x p) '' P f) (afun x p) :=
    ⟨⟨p, hp, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; rw [hpv]; exact weak y hy h1 hxy hq⟩
  have he : env f x = afun x p := hG.csSup_eq
  exact ⟨p, hp, he, fun q hq => he ▸ hG.2 ⟨q, hq, rfl⟩, y, hy, h1, hxy, he.trans hpv⟩

lemma vb_mem {n : ℕ} (b : Fin n → Bool) : vb b ∈ binaryPoints n := fun i => by
  unfold vb; split_ifs <;> simp

lemma jensen {n : ℕ} {f h : (Fin n → ℝ) → ℝ} (hh : IsConvexUnderestimator (binaryPoints n) f h)
    {x : Fin n → ℝ} (y : (Fin n → Bool) → ℝ) (hy : ∀ b, 0 ≤ y b) (h1 : ∑ b, y b = 1)
    (hx : ∑ b, y b • vb b = x) : h x ≤ ∑ b, y b * f (vb b) := by
  have hj := hh.1.map_sum_le (t := Finset.univ) (w := y) (p := vb) (fun b _ => hy b) h1
    (fun b _ => subset_convexHull ℝ _ (vb_mem b))
  rw [hx] at hj
  refine hj.trans (Finset.sum_le_sum fun b _ => ?_)
  rw [smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (hh.2 _ (vb_mem b)) (hy b)

lemma p0_mem {n : ℕ} (f : (Fin n → ℝ) → ℝ) : ((0 : Fin n → ℝ), -∑ b, |f (vb b)|) ∈ P f := by
  intro b
  show (0 : Fin n → ℝ) ⬝ᵥ vb b + -∑ b, |f (vb b)| ≤ f (vb b)
  have := Finset.single_le_sum (f := fun b => |f (vb b)|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ b)
  rw [zero_dotProduct]
  linarith [neg_abs_le (f (vb b))]

open Classical in
noncomputable def piece {n : ℕ} (f : (Fin n → ℝ) → ℝ) (T : Finset (Fin n → Bool)) : E n :=
  if h : ∃ p ∈ P f, ∀ q : E n, (∀ b ∈ T, afun (vb b) q = f (vb b)) → q = p then h.choose
  else ((0 : Fin n → ℝ), -∑ b, |f (vb b)|)

lemma piece_eq {n : ℕ} (f : (Fin n → ℝ) → ℝ) (T : Finset (Fin n → Bool)) (p : E n)
    (hp : p ∈ P f) (hT : ∀ b ∈ T, afun (vb b) p = f (vb b))
    (hu : ∀ q : E n, (∀ b ∈ T, afun (vb b) q = f (vb b)) → q = p) : piece f T = p := by
  have h : ∃ p ∈ P f, ∀ q : E n, (∀ b ∈ T, afun (vb b) q = f (vb b)) → q = p := ⟨p, hp, hu⟩
  unfold piece
  rw [dif_pos h]
  exact (h.choose_spec.2 p hT).symm

lemma piece_mem {n : ℕ} (f : (Fin n → ℝ) → ℝ) (T : Finset (Fin n → Bool)) : piece f T ∈ P f := by
  unfold piece
  split_ifs with h
  · exact h.choose_spec.1
  · exact p0_mem f

lemma pointed {n : ℕ} (d : E n) (h : ∀ b, afun (vb b) d = 0) : d = 0 := by
  have h0 : d.2 = 0 := by
    have := h (fun _ => false)
    have hz : vb (fun _ : Fin n => false) = 0 := by funext i; simp [vb]
    rw [afun_apply, hz, dotProduct_zero, zero_add] at this
    exact this
  have h1 : ∀ j, d.1 j = 0 := by
    intro j
    have := h (fun i => decide (i = j))
    have hz : vb (fun i => decide (i = j)) = Pi.single j 1 := by
      funext i; simp [vb, Pi.single_apply]
    rw [afun_apply, hz, dotProduct_single, h0, add_zero, mul_one] at this
    exact this
  exact Prod.ext (funext h1) h0

lemma spike {n : ℕ} (f : (Fin n → ℝ) → ℝ) {v : Fin n → ℝ} (hv : v ∈ binaryPoints n) :
    ∃ p ∈ P f, afun v p = f v := by
  set M : ℝ := ∑ b, |f (vb b) - f v| with hM
  let α : Fin n → ℝ := fun i => M * (2 * v i - 1)
  let β : ℝ := f v - ∑ i, M * (2 * v i - 1) * v i
  have hval : ∀ u : Fin n → ℝ, afun u (α, β) = f v + M * ∑ i, (2 * v i - 1) * (u i - v i) := by
    intro u
    simp only [afun_apply, dotProduct, α, β, Finset.mul_sum]
    rw [show ∑ i, M * ((2 * v i - 1) * (u i - v i)) =
        ∑ i, M * (2 * v i - 1) * u i - ∑ i, M * (2 * v i - 1) * v i from by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring]
    ring
  refine ⟨(α, β), fun b => ?_, by rw [hval]; simp⟩
  rw [hval]
  have hterm : ∀ i, (2 * v i - 1) * (vb b i - v i) ≤ 0 := by
    intro i
    unfold vb
    rcases hv i with h | h <;> split_ifs <;> simp [h] <;> norm_num
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases heq : vb b = v
  · rw [heq]; simp
  · obtain ⟨i, hi⟩ : ∃ i, vb b i ≠ v i := by
      by_contra hc; push Not at hc; exact heq (funext hc)
    have hti : (2 * v i - 1) * (vb b i - v i) = -1 := by
      unfold vb at hi ⊢
      rcases hv i with h | h <;> split_ifs at hi ⊢ <;> simp_all <;> norm_num
    have hs := Finset.single_le_sum (f := fun j => -((2 * v j - 1) * (vb b j - v j)))
      (fun j _ => by linarith [hterm j]) (Finset.mem_univ i)
    simp only [hti, Finset.sum_neg_distrib] at hs
    have hMb : f v - f (vb b) ≤ M := by
      have := Finset.single_le_sum (f := fun b => |f (vb b) - f v|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ b)
      linarith [neg_abs_le (f (vb b) - f v)]
    have : M * ∑ j, (2 * v j - 1) * (vb b j - v j) ≤ -M := by nlinarith
    linarith

end

section

open SDDiP.Envelope in
theorem solution (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (∃ e : (Fin n → ℝ) → ℝ, IsConvexLowerEnvelope (binaryPoints n) f e) ∧
    ∀ e : (Fin n → ℝ) → ℝ, IsConvexLowerEnvelope (binaryPoints n) f e →
      ConvexOn ℝ (cube n) e ∧ IsMaxOfAffineOn (cube n) e ∧
      ∀ x ∈ binaryPoints n, e x = f x := by
  have hVc : binaryPoints n ⊆ cube n := fun v hv => by
    rw [← hull_eq]; exact subset_convexHull ℝ _ hv
  refine ⟨⟨env f, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [hull_eq]
    refine ⟨cube_convex n, fun x hx x' hx' a b ha hb hab => ?_⟩
    have hz : a • x + b • x' ∈ cube n := cube_convex n hx hx' ha hb hab
    obtain ⟨p, hp, hpe, -, -⟩ := env_spec f hz
    obtain ⟨-, -, -, hub, -⟩ := env_spec f hx
    obtain ⟨-, -, -, hub', -⟩ := env_spec f hx'
    rw [hpe, afun_comb x x' p a b hab, smul_eq_mul, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hub p hp) ha
    have h2 := mul_le_mul_of_nonneg_left (hub' p hp) hb
    linarith
  · intro v hv
    obtain ⟨p, hp, hpe, -, -⟩ := env_spec f (hVc hv)
    rw [hpe, eq_vb hv]
    exact hp _
  · intro h hh x hx
    rw [hull_eq] at hx
    obtain ⟨-, -, -, -, y, hy, h1, hxy, hev⟩ := env_spec f hx
    rw [hev]
    exact jensen hh y hy h1 hxy
  intro e he
  have lb : ∀ p ∈ P f, ∀ x ∈ cube n, afun x p ≤ e x := fun p hp x hx =>
    he.2 _ (affine_under hp) x (by rw [hull_eq]; exact hx)
  refine ⟨by rw [← hull_eq]; exact he.1.1, ?_, ?_⟩
  · classical
    let eqv := Fintype.equivFin (Finset (Fin n → Bool))
    refine ⟨Fintype.card (Finset (Fin n → Bool)), fun k => (piece f (eqv.symm k)).1,
      fun k => (piece f (eqv.symm k)).2, fun x hx => ⟨fun k => lb _ (piece_mem f _) x hx, ?_⟩⟩
    obtain ⟨p, hp, y, hy, h1, hxy, hpv⟩ := key f hx
    -- complementary slackness
    have hcs : ∀ b, y b = 0 ∨ afun (vb b) p = f (vb b) := by
      have hsum : ∑ b, y b * (f (vb b) - afun (vb b) p) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib]
        rw [← eval y h1 hxy p, hpv, sub_self]
      have hnn : ∀ b ∈ Finset.univ, 0 ≤ y b * (f (vb b) - afun (vb b) p) := fun b _ =>
        mul_nonneg (hy b) (by linarith [hp b])
      intro b
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum b (Finset.mem_univ b)
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    obtain ⟨p', hp', htp, hu⟩ := descent (fun b => afun (vb b)) (fun b => f (vb b))
      (fun d hd => pointed d hd) _ p hp rfl
    let T : Finset (Fin n → Bool) := Finset.univ.filter fun b => afun (vb b) p' = f (vb b)
    have hpc : piece f T = p' := piece_eq f T p' hp'
      (fun b hb => (Finset.mem_filter.mp hb).2)
      (fun q hq => hu q (fun b hb => hq b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)))
    refine ⟨eqv T, ?_⟩
    show e x = (piece f (eqv.symm (eqv T))).1 ⬝ᵥ x + (piece f (eqv.symm (eqv T))).2
    rw [Equiv.symm_apply_apply, hpc]
    show e x = afun x p'
    have hval : afun x p' = ∑ b, y b * f (vb b) := by
      rw [eval y h1 hxy p']
      refine Finset.sum_congr rfl fun b _ => ?_
      rcases hcs b with h | h
      · rw [h, zero_mul, zero_mul]
      · rw [htp b h]
    have hup : e x ≤ ∑ b, y b * f (vb b) := jensen he.1 y hy h1 hxy
    have hlow := lb p hp x hx
    rw [hpv] at hlow
    linarith
  · intro v hv
    obtain ⟨p, hp, hpv⟩ := spike f hv
    have h1 := lb p hp v (hVc hv)
    have h2 := he.1.2 v hv
    linarith

end
