-- Prove2me | solution 1 for RLCDiscrepancy.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:28:20.738261+00:00
-- url     : https://prove2.me/submissions/e52f533a-ebd7-46e5-83f3-323bbc3cf97c

import Mathlib
import Definitions.Def_RLCDiscrepancy_IsNormalized
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_RLCDiscrepancy_l2NormSq
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_RLCDiscrepancy_rlc

section
set_option autoImplicit false
namespace RLCDiscrepancy.Dev.L44

open Finset

theorem sum_comp_surj {A B : Type*} [AddCommGroup A] [Fintype A] [AddCommGroup B] [Fintype B]
    [DecidableEq B] (Φ : A →+ B) (hΦ : Function.Surjective Φ) (φ : B → ℝ) :
    (Fintype.card B : ℝ) * ∑ a, φ (Φ a) = Fintype.card A * ∑ b, φ b := by
  set K := #{a | Φ a = 0} with hK
  have hfib : ∀ b, #{a | Φ a = b} = K := fun b =>
    AddMonoidHom.card_fiber_eq_of_mem_range Φ (hΦ b) (hΦ 0)
  have hcard : Fintype.card A = Fintype.card B * K := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := Φ) (t := univ) (by simp)]
    simp [hfib]
  have hsum : ∑ a, φ (Φ a) = ∑ b, (K : ℝ) * φ b := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Φ) (t := univ) (fun _ _ => mem_univ _)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => φ b) (fun a ha => by rw [(mem_filter.1 ha).2])]
    simp [hfib]
  rw [hsum, ← Finset.mul_sum, hcard]; push_cast; ring

/-- the evaluation hom `G ↦ G v`. -/
def evHom {F : Type*} [Field F] [Fintype F] (n m : ℕ) (v : Fin m → F) :
    Matrix (Fin n) (Fin m) F →+ (Fin n → F) where
  toFun G := G.mulVec v
  map_add' G H := Matrix.add_mulVec G H v
  map_zero' := Matrix.zero_mulVec v

def evHom2 {F : Type*} [Field F] [Fintype F] (n m : ℕ) (v v' : Fin m → F) :
    Matrix (Fin n) (Fin m) F →+ (Fin n → F) × (Fin n → F) where
  toFun G := (G.mulVec v, G.mulVec v')
  map_add' G H := by simp [Matrix.add_mulVec]
  map_zero' := by simp

theorem evHom_surj {F : Type*} [Field F] [Fintype F] (n m : ℕ) (v : Fin m → F) (hv : v ≠ 0) :
    Function.Surjective (evHom n m v) := by
  intro w
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  refine ⟨Matrix.of fun i k => if k = j then w i / v j else 0, ?_⟩
  funext i
  simp [evHom, Matrix.mulVec, dotProduct, hj]

theorem evHom2_surj {F : Type*} [Field F] [Fintype F] (n m : ℕ) (v v' : Fin m → F)
    (hind : LinearIndependent F ![v, v']) :
    Function.Surjective (evHom2 n m v v') := by
  classical
  -- surjectivity of r ↦ (v ⬝ r, v' ⬝ r)
  let T : (Fin m → F) →ₗ[F] F × F :=
    { toFun := fun r => (v ⬝ᵥ r, v' ⬝ᵥ r)
      map_add' := fun r s => by simp [dotProduct_add]
      map_smul' := fun c r => by simp [dotProduct_smul] }
  have hT : ∀ r, T r = (v ⬝ᵥ r, v' ⬝ᵥ r) := fun r => by simp [T]
  have hTs : Function.Surjective T := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    have hlt : LinearMap.range T < ⊤ := lt_top_iff_ne_top.2 hne
    obtain ⟨g, hg0, hg⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    have hgr : ∀ r, g (T r) = 0 := by
      intro r
      have h1 : g (T r) ∈ (LinearMap.range T).map g :=
        Submodule.mem_map_of_mem (LinearMap.mem_range_self T r)
      rw [hg] at h1
      exact Submodule.mem_bot F |>.1 h1
    have hg' : ∀ p : F × F, g p = p.1 * g (1, 0) + p.2 * g (0, 1) := by
      intro p
      have : p = p.1 • ((1 : F), (0 : F)) + p.2 • ((0 : F), (1 : F)) := by ext <;> simp
      conv_lhs => rw [this]
      simp only [map_add, map_smul, smul_eq_mul]
    have hab : g (1, 0) • v + g (0, 1) • v' = 0 := by
      funext k
      have := hgr (Pi.single k 1)
      rw [hT, hg'] at this
      simpa [mul_comm] using this
    have := LinearIndependent.pair_iff.1 hind (g (1, 0)) (g (0, 1)) hab
    apply hg0
    exact LinearMap.ext fun p => by rw [hg' p, this.1, this.2]; simp
  choose r hr using hTs
  rintro ⟨w, w'⟩
  refine ⟨Matrix.of fun i => r (w i, w' i), ?_⟩
  have key : ∀ i, (v ⬝ᵥ r (w i, w' i), v' ⬝ᵥ r (w i, w' i)) = (w i, w' i) := fun i => by
    rw [← hT, hr]
  ext i
  · have := congrArg Prod.fst (key i)
    simp only [evHom2, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, Matrix.of_apply] at this ⊢
    rw [dotProduct_comm]; exact this
  · have := congrArg Prod.snd (key i)
    simp only [evHom2, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, Matrix.of_apply] at this ⊢
    rw [dotProduct_comm]; exact this


open scoped Classical

variable {F : Type*} [Field F] [Fintype F] {n m : ℕ}

theorem card_ev_fiber (v : Fin m → F) (hv : v ≠ 0) :
    (Fintype.card (Fin n → F) : ℝ) * (#{G : Matrix (Fin n) (Fin m) F | G.mulVec v = 0} : ℝ) =
      Fintype.card (Matrix (Fin n) (Fin m) F) := by
  have := sum_comp_surj (evHom n m v) (evHom_surj n m v hv) (fun w => if w = 0 then (1 : ℝ) else 0)
  have e : ∑ G : Matrix (Fin n) (Fin m) F, (if evHom n m v G = 0 then (1 : ℝ) else 0) =
      (#{G : Matrix (Fin n) (Fin m) F | G.mulVec v = 0} : ℝ) := by
    rw [Finset.sum_boole]; rfl
  rw [e] at this
  simpa using this

theorem sum_ev (v : Fin m → F) (hv : v ≠ 0) (φ : (Fin n → F) → ℝ) :
    (Fintype.card (Fin n → F) : ℝ) * ∑ G : Matrix (Fin n) (Fin m) F, φ (G.mulVec v) =
      Fintype.card (Matrix (Fin n) (Fin m) F) * ∑ w, φ w :=
  sum_comp_surj (evHom n m v) (evHom_surj n m v hv) φ

theorem pair_zero (h : (Fin n → F) → ℝ) (hh : ∑ w, h w = 0) (v v' : Fin m → F)
    (hind : LinearIndependent F ![v, v']) :
    ∑ G : Matrix (Fin n) (Fin m) F, h (G.mulVec v) * h (G.mulVec v') = 0 := by
  have := sum_comp_surj (evHom2 n m v v') (evHom2_surj n m v v' hind) (fun p => h p.1 * h p.2)
  have hc : (Fintype.card ((Fin n → F) × (Fin n → F)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h2 : ∑ p : (Fin n → F) × (Fin n → F), h p.1 * h p.2 = 0 := by
    rw [Fintype.sum_prod_type]; simp [← Finset.mul_sum, hh]
  rw [h2, mul_zero] at this
  simpa [evHom2, hc] using this

theorem dep_bound (h : (Fin n → F) → ℝ) (v : Fin m → F) (hv : v ≠ 0) (c : F) (hc : c ≠ 0) :
    ∑ G : Matrix (Fin n) (Fin m) F, h (G.mulVec v) * h (G.mulVec (c • v)) ≤
      (Fintype.card (Matrix (Fin n) (Fin m) F) : ℝ) / Fintype.card (Fin n → F) * ∑ w, h w ^ 2 := by
  have hq : (Fintype.card (Fin n → F) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : ∑ G : Matrix (Fin n) (Fin m) F, h (G.mulVec v) * h (G.mulVec (c • v)) ≤
      ∑ G : Matrix (Fin n) (Fin m) F, (h (G.mulVec v) ^ 2 + h (c • G.mulVec v) ^ 2) / 2 := by
    refine Finset.sum_le_sum fun G _ => ?_
    rw [Matrix.mulVec_smul]
    nlinarith [sq_nonneg (h (G.mulVec v) - h (c • G.mulVec v))]
  refine h1.trans (le_of_eq ?_)
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have e1 := sum_ev v hv (fun w => h w ^ 2)
  have e2 := sum_ev v hv (fun w => h (c • w) ^ 2)
  have hb : ∑ w : Fin n → F, h (c • w) ^ 2 = ∑ w, h w ^ 2 :=
    Fintype.sum_bijective (fun w => c • w)
      ((Finite.injective_iff_bijective).1 (smul_right_injective _ hc)) _ _ (fun _ => rfl)
  rw [hb] at e2
  field_simp
  linarith

omit [Field F] in
theorem card_pi_real (k : ℕ) : (Fintype.card (Fin k → F) : ℝ) = (Fintype.card F : ℝ) ^ k := by
  simp

theorem card_nz : (#{c : F | c ≠ 0} : ℝ) = (Fintype.card F : ℝ) - 1 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
    Nat.cast_sub Fintype.card_pos]
  simp

theorem rank_bound :
    ((Fintype.card F : ℝ) - 1) *
        (#{G : Matrix (Fin n) (Fin m) F | ∃ v : Fin m → F, v ≠ 0 ∧ G.mulVec v = 0} : ℝ) ≤
      (Fintype.card F : ℝ) ^ m * Fintype.card (Matrix (Fin n) (Fin m) F) /
        (Fintype.card F : ℝ) ^ n := by
  set B1 : Finset (Matrix (Fin n) (Fin m) F) := {G | ∃ v : Fin m → F, v ≠ 0 ∧ G.mulVec v = 0} with hB1
  set S : Finset (Fin m → F) := {v | v ≠ 0} with hS
  have key : ∀ G ∈ B1, ((Fintype.card F : ℝ) - 1) ≤ (#{v ∈ S | G.mulVec v = 0} : ℝ) := by
    intro G hG
    obtain ⟨v0, hv0, hG0⟩ := (mem_filter.1 hG).2
    rw [← card_nz]
    have hinj : Function.Injective (fun c : F => c • v0) := smul_left_injective F hv0
    have hsub : (Finset.image (fun c : F => c • v0) {c : F | c ≠ 0}).card ≤ #{v ∈ S | G.mulVec v = 0} := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hx
      have hc' : c ≠ 0 := (mem_filter.1 hc).2
      refine mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, smul_ne_zero hc' hv0⟩, ?_⟩
      rw [Matrix.mulVec_smul, hG0, smul_zero]
    rw [Finset.card_image_of_injective _ hinj] at hsub
    exact_mod_cast hsub
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) ^ n := by positivity
  have h1 : ((Fintype.card F : ℝ) - 1) * (#B1 : ℝ) ≤
      ∑ G : Matrix (Fin n) (Fin m) F, (#{v ∈ S | G.mulVec v = 0} : ℝ) := by
    calc ((Fintype.card F : ℝ) - 1) * (#B1 : ℝ) = ∑ G ∈ B1, ((Fintype.card F : ℝ) - 1) := by
          simp [mul_comm]; ring
      _ ≤ ∑ G ∈ B1, (#{v ∈ S | G.mulVec v = 0} : ℝ) := Finset.sum_le_sum key
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
  have h2 : ∑ G : Matrix (Fin n) (Fin m) F, (#{v ∈ S | G.mulVec v = 0} : ℝ) =
      ∑ v ∈ S, (Fintype.card (Matrix (Fin n) (Fin m) F) : ℝ) / (Fintype.card F : ℝ) ^ n := by
    have : ∀ G : Matrix (Fin n) (Fin m) F, (#{v ∈ S | G.mulVec v = 0} : ℝ) =
        ∑ v ∈ S, (if G.mulVec v = 0 then (1 : ℝ) else 0) := fun G => by
      rw [Finset.sum_boole]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv' : v ≠ 0 := (mem_filter.1 hv).2
    have := card_ev_fiber (n := n) v hv'
    rw [card_pi_real] at this
    rw [Finset.sum_boole, eq_div_iff hq.ne', ← this]; ring
  rw [h2, Finset.sum_const, nsmul_eq_mul] at h1
  refine h1.trans ?_
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hq.le
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have : #S ≤ Fintype.card (Fin m → F) := Finset.card_le_univ _
  rw [← card_pi_real]; exact_mod_cast this

theorem inner_bound (h : (Fin n → F) → ℝ) (hh : ∑ w, h w = 0) (v : Fin m → F) (hv : v ≠ 0) :
    ∑ v' ∈ ({v | v ≠ 0} : Finset (Fin m → F)),
        ∑ G : Matrix (Fin n) (Fin m) F, h (G.mulVec v) * h (G.mulVec v') ≤
      ((Fintype.card F : ℝ) - 1) *
        ((Fintype.card (Matrix (Fin n) (Fin m) F) : ℝ) / Fintype.card (Fin n → F) *
          ∑ w, h w ^ 2) := by
  set B : ℝ := (Fintype.card (Matrix (Fin n) (Fin m) F) : ℝ) / Fintype.card (Fin n → F) *
    ∑ w, h w ^ 2 with hB
  have hB0 : 0 ≤ B := by
    rw [hB]; positivity
  set S : Finset (Fin m → F) := {v | v ≠ 0} with hS
  set D : Finset (Fin m → F) := S.filter (fun v' => ¬ LinearIndependent F ![v, v']) with hD
  rw [← Finset.sum_filter_add_sum_filter_not S (fun v' => ¬ LinearIndependent F ![v, v'])]
  have hz : ∑ v' ∈ S.filter (fun v' => ¬¬ LinearIndependent F ![v, v']),
      ∑ G : Matrix (Fin n) (Fin m) F, h (G.mulVec v) * h (G.mulVec v') = 0 :=
    Finset.sum_eq_zero fun v' hv' => pair_zero h hh v v' (not_not.1 (mem_filter.1 hv').2)
  rw [hz, add_zero]
  have hle : ∀ v' ∈ D, ∑ G : Matrix (Fin n) (Fin m) F, h (G.mulVec v) * h (G.mulVec v') ≤ B := by
    intro v' hv'
    have hv'0 : v' ≠ 0 := (mem_filter.1 (mem_filter.1 hv').1).2
    have hnot := (mem_filter.1 hv').2
    rw [LinearIndependent.pair_iff] at hnot
    push Not at hnot
    obtain ⟨s, t, hst, hne⟩ := hnot
    have ht : t ≠ 0 := by
      rintro rfl
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      rcases hst with rfl | h0
      · simp at hne
      · exact hv h0
    have hv'eq : v' = (-s / t) • v := by
      have : t • v' = -(s • v) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
      rw [div_eq_inv_mul, mul_smul, neg_smul, ← this, smul_smul, inv_mul_cancel₀ ht, one_smul]
    have hc : (-s / t) ≠ 0 := by
      intro h0; rw [h0, zero_smul] at hv'eq; exact hv'0 hv'eq
    rw [hv'eq]
    exact dep_bound h v hv _ hc
  have hcard : (#D : ℝ) ≤ (Fintype.card F : ℝ) - 1 := by
    rw [← card_nz]
    have hsub : D ⊆ Finset.image (fun c : F => c • v) {c : F | c ≠ 0} := by
      intro v' hv'
      have hv'0 : v' ≠ 0 := (mem_filter.1 (mem_filter.1 hv').1).2
      have hnot := (mem_filter.1 hv').2
      rw [LinearIndependent.pair_iff] at hnot
      push Not at hnot
      obtain ⟨s, t, hst, hne⟩ := hnot
      have ht : t ≠ 0 := by
        rintro rfl
        rw [zero_smul, add_zero, smul_eq_zero] at hst
        rcases hst with rfl | h0
        · simp at hne
        · exact hv h0
      have hv'eq : v' = (-s / t) • v := by
        have : t • v' = -(s • v) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
        rw [div_eq_inv_mul, mul_smul, neg_smul, ← this, smul_smul, inv_mul_cancel₀ ht, one_smul]
      have hc : (-s / t) ≠ 0 := by
        intro h0; rw [h0, zero_smul] at hv'eq; exact hv'0 hv'eq
      exact Finset.mem_image.2 ⟨-s / t, mem_filter.2 ⟨mem_univ _, hc⟩, hv'eq.symm⟩
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  calc _ ≤ ∑ v' ∈ S.filter (fun v' => ¬ LinearIndependent F ![v, v']), B := Finset.sum_le_sum hle
    _ = (#D : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hB0

theorem second_moment (h : (Fin n → F) → ℝ) (hh : ∑ w, h w = 0) :
    ∑ G : Matrix (Fin n) (Fin m) F, (∑ v ∈ ({v | v ≠ 0} : Finset (Fin m → F)), h (G.mulVec v)) ^ 2 ≤
      (Fintype.card F : ℝ) ^ m * (((Fintype.card F : ℝ) - 1) *
        ((Fintype.card (Matrix (Fin n) (Fin m) F) : ℝ) / (Fintype.card F : ℝ) ^ n *
          ∑ w, h w ^ 2)) := by
  set S : Finset (Fin m → F) := {v | v ≠ 0} with hS
  have e : ∑ G : Matrix (Fin n) (Fin m) F, (∑ v ∈ S, h (G.mulVec v)) ^ 2 =
      ∑ v ∈ S, ∑ v' ∈ S, ∑ G : Matrix (Fin n) (Fin m) F, h (G.mulVec v) * h (G.mulVec v') := by
    simp only [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_comm]
  rw [e]
  have hq : (Fintype.card (Fin n → F) : ℝ) = (Fintype.card F : ℝ) ^ n := card_pi_real n
  calc _ ≤ ∑ v ∈ S, ((Fintype.card F : ℝ) - 1) *
        ((Fintype.card (Matrix (Fin n) (Fin m) F) : ℝ) / Fintype.card (Fin n → F) * ∑ w, h w ^ 2) :=
        Finset.sum_le_sum fun v hv => inner_bound h hh v (mem_filter.1 hv).2
    _ = (#S : ℝ) * (((Fintype.card F : ℝ) - 1) *
        ((Fintype.card (Matrix (Fin n) (Fin m) F) : ℝ) / Fintype.card (Fin n → F) * ∑ w, h w ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        rw [hq]
        have hS' : (#S : ℝ) ≤ (Fintype.card F : ℝ) ^ m := by
          rw [← card_pi_real]; exact_mod_cast Finset.card_le_univ _
        have hF : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
        apply mul_le_mul_of_nonneg_right hS'
        have : 0 ≤ ((Fintype.card F : ℝ) - 1) := by linarith
        positivity

theorem relDev_inj (f : (Fin n → F) → ℝ) (G : Matrix (Fin n) (Fin m) F)
    (hG : ¬ ∃ v : Fin m → F, v ≠ 0 ∧ G.mulVec v = 0) :
    relDev (rlc G) f = ((f 0 - 1) + ∑ v ∈ ({v | v ≠ 0} : Finset (Fin m → F)),
      (f (G.mulVec v) - 1)) / (Fintype.card F : ℝ) ^ m := by
  have hinj : Function.Injective (fun v : Fin m → F => G.mulVec v) := by
    intro v v' hvv
    by_contra hne
    apply hG
    refine ⟨v - v', sub_ne_zero.2 hne, ?_⟩
    rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hvv
  have hcode : codeFinset (rlc G) = Finset.univ.image (fun v : Fin m → F => G.mulVec v) := by
    ext x
    simp [mem_codeFinset, rlc, LinearMap.mem_range]
  have hcard : ((codeFinset (rlc G)).card : ℝ) = (Fintype.card F : ℝ) ^ m := by
    rw [hcode, Finset.card_image_of_injective _ hinj]; simp
  have hsum : ∑ x ∈ codeFinset (rlc G), f x = ∑ v : Fin m → F, f (G.mulVec v) := by
    rw [hcode, Finset.sum_image (fun a _ b _ hab => hinj hab)]
  have hS : ({v | v ≠ 0} : Finset (Fin m → F)) = Finset.univ.erase 0 := Finset.filter_ne' _ _
  have hSc : (#({v | v ≠ 0} : Finset (Fin m → F)) : ℝ) = (Fintype.card F : ℝ) ^ m - 1 := by
    rw [hS, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
      Nat.cast_sub Fintype.card_pos]
    simp
  have hq : (Fintype.card F : ℝ) ^ m ≠ 0 := by positivity
  unfold relDev
  rw [hsum, hcard, ← Finset.add_sum_erase _ _ (mem_univ (0 : Fin m → F)), ← hS,
    Finset.sum_sub_distrib]
  simp only [Matrix.mulVec_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hSc]
  field_simp
  ring

theorem main_bound (n m : ℕ)
    (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (Δ : ℝ)
    (hΔ : ((Fintype.card F : ℝ) ^ m)⁻¹ * |f 0 - 1| < Δ) :
    PunctSketch.coinProb (fun G : Matrix (Fin n) (Fin m) F => Δ < |relDev (rlc G) f|) ≤
      ((Fintype.card F : ℝ) - 1) /
          ((Fintype.card F : ℝ) ^ m * (Δ - ((Fintype.card F : ℝ) ^ m)⁻¹ * |f 0 - 1|) ^ 2) *
          l2NormSq f +
        (Fintype.card F : ℝ) ^ ((m : ℝ) - n) / ((Fintype.card F : ℝ) - 1) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hq1 : 1 < q := by rw [hqdef]; exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  have hqm : 0 < q ^ m := by positivity
  have hqn : 0 < q ^ n := by positivity
  set N : ℝ := (Fintype.card (Matrix (Fin n) (Fin m) F) : ℝ) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast Fintype.card_pos
  set D : ℝ := Δ - (q ^ m)⁻¹ * |f 0 - 1| with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  set L : ℝ := l2NormSq f with hL
  have hL0 : 0 ≤ L := by
    rw [hL]; unfold l2NormSq; positivity
  set h : (Fin n → F) → ℝ := fun w => f w - 1 with hh
  have hh0 : ∑ w, h w = 0 := by
    simp only [hh, Finset.sum_sub_distrib]
    rw [hf.2]; simp [hqdef]
  have hh2 : ∑ w, h w ^ 2 ≤ q ^ n * L := by
    have : ∑ w, h w ^ 2 = ∑ w, f w ^ 2 - q ^ n := by
      have e : ∀ w, h w ^ 2 = f w ^ 2 - 2 * f w + 1 := by intro w; simp only [hh]; ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hf.2]
      simp [hqdef]; ring
    rw [this, hL]; unfold l2NormSq
    rw [← hqdef, mul_div_cancel₀ _ hqn.ne']
    linarith
  set Y : Matrix (Fin n) (Fin m) F → ℝ := fun G =>
    ∑ v ∈ ({v | v ≠ 0} : Finset (Fin m → F)), h (G.mulVec v) with hY
  set B1 : Finset (Matrix (Fin n) (Fin m) F) :=
    {G | ∃ v : Fin m → F, v ≠ 0 ∧ G.mulVec v = 0} with hB1
  set t : ℝ := q ^ m * D with ht
  have ht0 : 0 < t := by positivity
  set P : Finset (Matrix (Fin n) (Fin m) F) := {G | t ^ 2 ≤ Y G ^ 2} with hP
  have hcov : ∀ G : Matrix (Fin n) (Fin m) F, Δ < |relDev (rlc G) f| → G ∈ B1 ∪ P := by
    intro G hG
    by_cases hb : ∃ v : Fin m → F, v ≠ 0 ∧ G.mulVec v = 0
    · exact Finset.mem_union_left _ (mem_filter.2 ⟨mem_univ _, hb⟩)
    · refine Finset.mem_union_right _ (mem_filter.2 ⟨mem_univ _, ?_⟩)
      rw [relDev_inj f G hb] at hG
      have e : (f 0 - 1) + ∑ v ∈ ({v | v ≠ 0} : Finset (Fin m → F)), (f (G.mulVec v) - 1) =
          (f 0 - 1) + Y G := rfl
      rw [e, abs_div, abs_of_pos hqm, lt_div_iff₀ hqm] at hG
      have h2 : |f 0 - 1 + Y G| ≤ |f 0 - 1| + |Y G| := abs_add_le _ _
      have h3 : t ≤ |Y G| := by
        have : t = q ^ m * Δ - |f 0 - 1| := by
          rw [ht, hD]; field_simp
        linarith
      exact (sq_le_sq.2 (by rw [abs_of_pos ht0]; exact h3))
  have hrank := rank_bound (F := F) (n := n) (m := m)
  have hsm := second_moment (F := F) (n := n) (m := m) h hh0
  have hcardP : (#P : ℝ) * t ^ 2 ≤ ∑ G : Matrix (Fin n) (Fin m) F, Y G ^ 2 := by
    calc (#P : ℝ) * t ^ 2 = ∑ G ∈ P, t ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ G ∈ P, Y G ^ 2 := Finset.sum_le_sum fun G hG => (mem_filter.1 hG).2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
  have hsm' : ∑ G : Matrix (Fin n) (Fin m) F, Y G ^ 2 ≤ q ^ m * ((q - 1) * (N * L)) := by
    refine hsm.trans ?_
    apply mul_le_mul_of_nonneg_left _ hqm.le
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [div_mul_eq_mul_div, div_le_iff₀ hqn]
    calc N * ∑ w, h w ^ 2 ≤ N * (q ^ n * L) := mul_le_mul_of_nonneg_left hh2 hN.le
      _ = N * L * q ^ n := by ring
      _ ≤ _ := le_refl _
  have hc2 : (#P : ℝ) ≤ (q - 1) * L * N / (q ^ m * D ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    refine le_of_mul_le_mul_left ?_ hqm
    calc q ^ m * ((#P : ℝ) * (q ^ m * D ^ 2)) = (#P : ℝ) * t ^ 2 := by rw [ht]; ring
      _ ≤ _ := hcardP.trans hsm'
      _ = _ := by ring
  have hc1 : (#B1 : ℝ) ≤ q ^ m * N / q ^ n / (q - 1) := by
    rw [le_div_iff₀ (by linarith)]
    calc (#B1 : ℝ) * (q - 1) = (q - 1) * #B1 := by ring
      _ ≤ _ := hrank
  have hE : (#({G | Δ < |relDev (rlc G) f|} : Finset (Matrix (Fin n) (Fin m) F)) : ℝ) ≤
      #B1 + #P := by
    have : #({G | Δ < |relDev (rlc G) f|} : Finset (Matrix (Fin n) (Fin m) F)) ≤ #(B1 ∪ P) :=
      Finset.card_le_card fun G hG => hcov G (mem_filter.1 hG).2
    exact_mod_cast this.trans (Finset.card_union_le _ _)
  unfold PunctSketch.coinProb
  have hrp : q ^ ((m : ℝ) - n) = q ^ m / q ^ n := by
    rw [Real.rpow_sub (by linarith), Real.rpow_natCast, Real.rpow_natCast]
  rw [hrp]
  have hNN : (Fintype.card (Matrix (Fin n) (Fin m) F) : ℝ) = N := rfl
  rw [hNN, div_le_iff₀ hN]
  have e1 : (q - 1) / (q ^ m * D ^ 2) * L * N = (q - 1) * L * N / (q ^ m * D ^ 2) := by ring
  have e2 : q ^ m / q ^ n / (q - 1) * N = q ^ m * N / q ^ n / (q - 1) := by ring
  rw [add_mul, e1, e2]
  linarith [hE, hc1, hc2]

end RLCDiscrepancy.Dev.L44

namespace RLCDiscrepancy
open RLCDiscrepancy.Dev.L44 in
theorem chk_lemma_4_4 {F : Type*} [Field F] [Fintype F] (n m : ℕ) (hmn : m ≤ n)
    (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (Δ : ℝ)
    (hΔ : ((Fintype.card F : ℝ) ^ m)⁻¹ * |f 0 - 1| < Δ) :
    PunctSketch.coinProb (fun G : Matrix (Fin n) (Fin m) F => Δ < |relDev (rlc G) f|) ≤
      ((Fintype.card F : ℝ) - 1) /
          ((Fintype.card F : ℝ) ^ m * (Δ - ((Fintype.card F : ℝ) ^ m)⁻¹ * |f 0 - 1|) ^ 2) *
          l2NormSq f +
        (Fintype.card F : ℝ) ^ ((m : ℝ) - n) / ((Fintype.card F : ℝ) - 1) :=
  main_bound n m f hf Δ hΔ

end RLCDiscrepancy
end

theorem solution : type_of% @RLCDiscrepancy.chk_lemma_4_4 := @RLCDiscrepancy.chk_lemma_4_4
