-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P22.finiteFieldRealization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:54:29.016612+00:00
-- url     : https://prove2.me/submissions/53281a9e-4405-45b6-8b7b-b3415436fbac

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

namespace X8P22F
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix

def pm {ι : Type*} [DecidableEq ι] (e : ι ≃ ι) : Op ι := fun p q => if p = e q then 1 else 0

theorem x8_pm_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι) (p : ι) (f : ι → ℂ) :
    ∑ q, (if p = e q then f q else 0) = f (e.symm p) := by
  rw [Finset.sum_eq_single (e.symm p)]
  · simp
  · intro q _ hq; rw [if_neg]; intro h; apply hq; rw [h]; simp
  · simp

theorem x8_pm_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι) :
    pm e ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext p p'
  simp only [mul_apply, star_apply, pm, one_apply]
  have : ∀ q, (if p = e q then (1 : ℂ) else 0) * star (if p' = e q then (1 : ℂ) else 0) =
      if p = e q then (if p' = e q then 1 else 0) else 0 := by
    intro q; split_ifs <;> simp
  simp only [this, x8_pm_sum]
  by_cases h : p = p'
  · subst h; simp
  · rw [if_neg (by simpa using Ne.symm h), if_neg h]

theorem x8_pm_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι) (Y : Op ι) (p q : ι) :
    (pm e * Y * (pm e)ᴴ) p q = Y (e.symm p) (e.symm q) := by
  simp only [mul_apply, conjTranspose_apply, pm]
  have : ∀ j, (∑ i, (if p = e i then (1 : ℂ) else 0) * Y i j) = Y (e.symm p) j := by
    intro j
    rw [← x8_pm_sum e p (fun i => Y i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  simp only [this]
  rw [← x8_pm_sum e q (fun j => Y (e.symm p) j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem x8_isChannel_of {I O κ : Type*} [Fintype I] [Fintype O] [DecidableEq I] [Fintype κ]
    (Phi : QAlgorithms.Superop I O) (F : κ → Matrix O I ℂ) (hF : ∑ k, (F k)ᴴ * F k = 1)
    (hPhi : ∀ X, Phi X = ∑ k, F k * X * (F k)ᴴ) : QAlgorithms.IsChannel Phi := by
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun n => F (e.symm n), ?_, fun X => ?_⟩
  · unfold QAlgorithms.IsKrausFamily; rw [← hF, ← e.symm.sum_comp]
  · rw [hPhi X, QAlgorithms.krausApply, ← e.symm.sum_comp]

theorem x8_trR_channel {I A B : Type*} [Fintype I] [Fintype A] [Fintype B] [DecidableEq I]
    [DecidableEq A] [DecidableEq B]
    (D : Matrix (A × B) I ℂ) (hD : Dᴴ * D = 1) :
    IsChannel (fun X => traceRight (conjSuperop D X)) := by
  refine x8_isChannel_of _ (fun c : B => Matrix.of fun u p => D (u, c) p) ?_ ?_
  · rw [← hD]
    ext p q
    simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, Fintype.sum_prod_type, of_apply]
    rw [Finset.sum_comm]
  · intro X
    ext u u'
    simp only [traceRight, conjSuperop, of_apply, Matrix.sum_apply, mul_apply, conjTranspose_apply]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def eE (lam : F) (h1 : lam ≠ 1) : (F × F) ≃ (F × F) where
  toFun q := (q.1 + q.2, q.1 + lam * q.2)
  invFun p := (p.1 - (p.2 - p.1) / (lam - 1), (p.2 - p.1) / (lam - 1))
  left_inv q := by
    have : lam - 1 ≠ 0 := sub_ne_zero.mpr h1
    ext <;> simp <;> field_simp <;> ring
  right_inv p := by
    have : lam - 1 ≠ 0 := sub_ne_zero.mpr h1
    ext <;> simp <;> field_simp <;> ring

def eD (lam : F) : (F × F) ≃ (F × F) where
  toFun q := (q.1 - lam * q.2, q.1 + (1 - lam) * q.2)
  invFun p := (p.1 + lam * (p.2 - p.1), p.2 - p.1)
  left_inv q := by ext <;> simp <;> ring
  right_inv p := by ext <;> simp <;> ring

theorem x8_enc (lam : F) (h1 : lam ≠ 1) : fieldEncoder lam = pm (eE lam h1) := by
  ext p q
  simp [fieldEncoder, pm, eE, Prod.ext_iff]

theorem x8_dec (lam : F) : fieldDecoder lam = pm (eD lam) := by
  ext p q
  simp [fieldDecoder, pm, eD, Prod.ext_iff]

theorem x8_auth (lam : F) (X : Op F) (s n s' n' : F) :
    fieldAuthorized lam X (s, n) (s', n') =
      if s - lam * n + n = s' - lam * n' + n' then X (s - lam * n) (s' - lam * n') / (Fintype.card F : ℂ)
      else 0 := by
  simp only [fieldAuthorized, fieldEncoder]
  have e1 : ∀ a b : F, (a = b + n ∧ s = b + lam * n) ↔ (b = s - lam * n ∧ a = s - lam * n + n) := by
    intro a b; constructor
    · rintro ⟨h1, h2⟩; constructor <;> [linear_combination -h2; linear_combination h1 - h2]
    · rintro ⟨h1, h2⟩; constructor <;> [linear_combination h2 - h1; linear_combination -h1]
  have e2 : ∀ a c : F, (a = c + n' ∧ s' = c + lam * n') ↔ (c = s' - lam * n' ∧ a = s' - lam * n' + n') := by
    intro a c; constructor
    · rintro ⟨h1, h2⟩; constructor <;> [linear_combination -h2; linear_combination h1 - h2]
    · rintro ⟨h1, h2⟩; constructor <;> [linear_combination h2 - h1; linear_combination -h1]
  simp only [e1, e2]
  have hs : ∀ a b c : F, (if b = s - lam * n ∧ a = s - lam * n + n then (1 : ℂ) else 0) * X b c *
      conj (if c = s' - lam * n' ∧ a = s' - lam * n' + n' then (1 : ℂ) else 0) / (Fintype.card F : ℂ) =
      if c = s' - lam * n' then (if b = s - lam * n then
        (if a = s - lam * n + n then (if s - lam * n + n = s' - lam * n' + n' then
          X b c / (Fintype.card F : ℂ) else 0) else 0) else 0) else 0 := by
    intro a b c
    by_cases hb : b = s - lam * n <;> by_cases hc : c = s' - lam * n' <;>
      by_cases ha : a = s - lam * n + n <;> simp [hb, hc, ha] <;> split_ifs <;> simp_all
  simp only [hs, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem x8_part5 (lam : F) (h0 : lam ≠ 0) (X : Op F) :
    traceRight (fieldAuthorized lam X) = X.trace • mixed F := by
  ext s s'
  rw [traceRight, of_apply]
  simp only [x8_auth]
  by_cases h : s = s'
  · subst h
    simp only [if_true]
    rw [← Finset.sum_div]
    let e : F ≃ F := ⟨fun n => s - lam * n, fun u => (s - u) / lam,
      fun n => by field_simp; ring, fun u => by field_simp; ring⟩
    have he : ∑ x, X (s - lam * x) (s - lam * x) = ∑ u, X u u := e.sum_comp (fun u => X u u)
    simp [he, mixed, trace, div_eq_mul_inv]
  · have : ∀ x : F, ¬ (s - lam * x + x = s' - lam * x + x) := by
      intro x h'; exact h (by linear_combination h')
    simp [this, mixed, h]

theorem x8_part6 (lam : F) (X : Op F) :
    traceRight (conjSuperop (fieldDecoder lam) (fieldAuthorized lam X)) = X := by
  ext u u'
  simp only [traceRight, of_apply, conjSuperop, x8_dec, x8_pm_conj]
  simp only [eD, Equiv.coe_fn_symm_mk, x8_auth]
  have hd : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : ∀ w : F, (if u + lam * (w - u) - lam * (w - u) + (w - u) = u' + lam * (w - u') - lam * (w - u') + (w - u')
      then X (u + lam * (w - u) - lam * (w - u)) (u' + lam * (w - u') - lam * (w - u')) / (Fintype.card F : ℂ)
      else 0) = X u u' / (Fintype.card F : ℂ) := by
    intro w
    rw [if_pos (by ring)]
    congr 2 <;> ring
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

def φ (lam : F) (u : F × F) : Fin 4 → F := ![u.1, u.1 + u.2, u.1 + lam * u.2, u.2]

theorem x8_φ_inj (lam : F) : Function.Injective (φ lam) := by
  intro u v h
  have h0 := congrFun h 0
  have h3 := congrFun h 3
  simp [φ] at h0 h3
  exact Prod.ext h0 h3

theorem x8_memS (lam : F) (p : Fin 4 → F) :
    (p 1 = p 0 + p 3 ∧ p 2 = p 0 + lam * p 3) ↔ p = φ lam (p 0, p 3) := by
  constructor
  · rintro ⟨h1, h2⟩
    funext i; fin_cases i <;> simp [φ, h1, h2]
  · intro h
    rw [h]; simp [φ]

theorem x8_sumS {M : Type*} [AddCommMonoid M] (lam : F) (g : (Fin 4 → F) → M)
    (hg : ∀ p, ¬(p 1 = p 0 + p 3 ∧ p 2 = p 0 + lam * p 3) → g p = 0) :
    ∑ p, g p = ∑ u, g (φ lam u) := by
  rw [show ∑ u, g (φ lam u) = ∑ x ∈ Finset.univ.map ⟨φ lam, x8_φ_inj lam⟩, g x from
    by rw [Finset.sum_map]; rfl]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  apply hg
  intro hS
  apply hp
  rw [Finset.mem_map]
  exact ⟨(p 0, p 3), Finset.mem_univ _, ((x8_memS lam p).mp hS).symm⟩

theorem x8_pairs : ∀ J : Finset (Fin 4), J.card = 2 →
    J = {0, 1} ∨ J = {0, 2} ∨ J = {0, 3} ∨ J = {1, 2} ∨ J = {1, 3} ∨ J = {2, 3} := by
  decide

theorem x8_pair (lam : F) (h0 : lam ≠ 0) (h1 : lam ≠ 1) (J : Finset (Fin 4)) (hJ : J.card = 2)
    (u v : F × F) (h : ∀ j ∈ J, φ lam u j = φ lam v j) : u = v := by
  obtain ⟨a, b⟩ := u
  obtain ⟨c, d⟩ := v
  have hl : lam - 1 ≠ 0 := sub_ne_zero.mpr h1
  rcases x8_pairs J hJ with rfl | rfl | rfl | rfl | rfl | rfl
  · have e0 := h 0 (by simp); have e1 := h 1 (by simp)
    simp [φ] at e0 e1
    exact Prod.ext e0 (by linear_combination e1 - e0)
  · have e0 := h 0 (by simp); have e1 := h 2 (by simp)
    simp [φ] at e0 e1
    have : lam * (b - d) = 0 := by linear_combination e1 - e0
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' h0
    · exact Prod.ext e0 (by linear_combination h')
  · have e0 := h 0 (by simp); have e1 := h 3 (by simp)
    simp [φ] at e0 e1
    exact Prod.ext e0 e1
  · have e0 := h 1 (by simp); have e1 := h 2 (by simp)
    simp [φ] at e0 e1
    have : (lam - 1) * (b - d) = 0 := by linear_combination e1 - e0
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hl
    · exact Prod.ext (by linear_combination e0 - h') (by linear_combination h')
  · have e0 := h 1 (by simp); have e1 := h 3 (by simp)
    simp [φ] at e0 e1
    exact Prod.ext (by linear_combination e0 - e1) e1
  · have e0 := h 2 (by simp); have e1 := h 3 (by simp)
    simp [φ] at e0 e1
    exact Prod.ext (by linear_combination e0 - lam * e1) e1

theorem x8_restr_bij (lam : F) (h0 : lam ≠ 0) (h1 : lam ≠ 1) (J : Finset (Fin 4)) (hJ : J.card = 2) :
    Function.Bijective (fun u : F × F => fun j : J => φ lam u j) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun u v h => x8_pair lam h0 h1 J hJ u v (fun j hj => congrFun h ⟨j, hj⟩), ?_⟩
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, hJ]
  ring

theorem x8_choi_apply (lam : F) (p : Fin 4 → F) :
    (fieldChoi lam).ofLp p = if p 1 = p 0 + p 3 ∧ p 2 = p 0 + lam * p 3 then (Fintype.card F : ℂ)⁻¹ else 0 := rfl

theorem x8_choi_φ (lam : F) (u : F × F) : (fieldChoi lam).ofLp (φ lam u) = (Fintype.card F : ℂ)⁻¹ := by
  rw [x8_choi_apply, if_pos]
  simp [φ]

theorem x8_part3 (lam : F) (h0 : lam ≠ 0) (h1 : lam ≠ 1) : AMEFour (fieldChoi lam) := by
  have hd : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨?_, fun J hJ => ?_⟩
  · rw [IsState, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    rw [x8_sumS lam (fun p => ‖fieldChoi lam p‖ ^ 2) (fun p hp => by simp [x8_choi_apply, hp])]
    simp only [x8_choi_φ, Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
    simp only [norm_inv, Complex.norm_natCast, inv_pow]
    have : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    push_cast
    field_simp
  · have hJc : Jᶜ.card = 2 := by rw [Finset.card_compl, hJ]; simp
    unfold mixed
    ext a b
    rw [Matrix.smul_apply, one_apply, smul_eq_mul]
    simp only [marginal, pureDensity, of_apply]
    rw [x8_sumS lam _ (fun p hp => by
      apply Finset.sum_eq_zero; intro y _; simp [x8_choi_apply, hp])]
    have hin : ∀ u : F × F, (∑ y : Fin 4 → F, if (∀ j : J, φ lam u j = a j) ∧ (∀ j : J, y j = b j) ∧
        (∀ w, w ∉ J → φ lam u w = y w) then (fieldChoi lam).ofLp (φ lam u) * conj ((fieldChoi lam).ofLp y) else 0) =
        if (∀ j : J, φ lam u j = a j) ∧ (∀ j : J, φ lam u j = b j) then
          ((Fintype.card F : ℂ)⁻¹ * conj ((Fintype.card F : ℂ)⁻¹)) else 0 := by
      intro u
      rw [x8_sumS lam _ (fun p hp => by simp [x8_choi_apply, hp])]
      rw [Finset.sum_eq_single u]
      · simp only [x8_choi_φ]
        by_cases hc : (∀ j : J, φ lam u j = a j) ∧ (∀ j : J, φ lam u j = b j)
        · rw [if_pos ⟨hc.1, hc.2, by simp⟩, if_pos hc]
        · rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩), if_neg hc]
      · intro v _ hv
        rw [if_neg]
        rintro ⟨-, -, h3⟩
        exact hv (x8_pair lam h0 h1 Jᶜ hJc v u (fun j hj => (h3 j (Finset.mem_compl.mp hj)).symm))
      · simp
    rw [Finset.sum_congr rfl (fun u _ => by convert hin u)]
    have hbij := x8_restr_bij lam h0 h1 J hJ
    let e := Equiv.ofBijective _ hbij
    have hsum := e.sum_comp (fun t : J → F => if (∀ j : J, t j = a j) ∧ (∀ j : J, t j = b j) then
      ((Fintype.card F : ℂ)⁻¹ * conj ((Fintype.card F : ℂ)⁻¹)) else 0)
    simp only [e, Equiv.ofBijective_apply] at hsum
    rw [hsum]
    have hab : ∀ t : J → F, ((∀ j : J, t j = a j) ∧ (∀ j : J, t j = b j)) ↔ (t = a ∧ a = b) := by
      intro t; constructor
      · rintro ⟨h1, h2⟩
        have ta : t = a := funext h1
        exact ⟨ta, by rw [← ta]; exact funext h2⟩
      · rintro ⟨rfl, rfl⟩; exact ⟨fun _ => rfl, fun _ => rfl⟩
    simp only [hab]
    by_cases h : a = b
    · subst h
      simp only [and_true, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
      rw [Fintype.card_fun, Fintype.card_coe, hJ, map_inv₀, Complex.conj_natCast]
      push_cast; ring
    · simp [h]

theorem x8_main (lam : F) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    fieldEncoder lam ∈ Matrix.unitaryGroup (F × F) ℂ ∧
    fieldDecoder lam ∈ Matrix.unitaryGroup (F × F) ℂ ∧ AMEFour (fieldChoi lam) ∧
    IsChannel (fun X => traceRight (conjSuperop (fieldDecoder lam) X)) ∧
    (∀ X : Op F, traceRight (fieldAuthorized lam X) = X.trace • mixed F) ∧
    (∀ X : Op F, traceRight (conjSuperop (fieldDecoder lam) (fieldAuthorized lam X)) = X) := by
  refine ⟨?_, ?_, x8_part3 lam h0 h1, ?_, x8_part5 lam h0, x8_part6 lam⟩
  · rw [x8_enc lam h1]; exact x8_pm_unitary _
  · rw [x8_dec]; exact x8_pm_unitary _
  · apply x8_trR_channel
    have := x8_pm_unitary (eD lam)
    rw [Matrix.mem_unitaryGroup_iff'] at this
    rw [x8_dec, ← Matrix.star_eq_conjTranspose]
    exact this

end X8P22F

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22


open scoped ComplexConjugate ComplexOrder Matrix


local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

open QAlgorithms.Papers.Independent.Information100.P22 in
/-- §S1.5, PDF p.25: explicit encoder, AME vector, concealment and decoder channel equality. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (hcard : Fintype.card F = 2^k) (lam : F) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    fieldEncoder lam ∈ Matrix.unitaryGroup (F × F) ℂ ∧
    fieldDecoder lam ∈ Matrix.unitaryGroup (F × F) ℂ ∧ AMEFour (fieldChoi lam) ∧
    IsChannel (fun X => traceRight (conjSuperop (fieldDecoder lam) X)) ∧
    (∀ X : Op F, traceRight (fieldAuthorized lam X) = X.trace • mixed F) ∧
    (∀ X : Op F, traceRight (conjSuperop (fieldDecoder lam) (fieldAuthorized lam X)) = X) :=
  X8P22F.x8_main lam h0 h1



