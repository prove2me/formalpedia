-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_variableChange_curve_eq_level_fst_eq_of_moduliPoint_mk_eq_of_raw_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/aa1e6cae-e42f-5aed-a826-cbff956b7992

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_ModuliPoint
import Theorems.Thm_ModularCurve_ModuliPoint_mk_eq_mk_iff_step
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_curve_eq_level_fst_eq_of_moduliPoint_mk_eq_of_raw_rigidDataH1Pow

set_option autoImplicit false

namespace AlignSol

open ModularCurve WeierstrassCurve WeierstrassCurve.Affine Polynomial

variable {K : Type} [Field K] [DecidableEq K]

def xco {W : WeierstrassCurve.Affine K} : W.Point → K
  | 0 => 0
  | .some x _ _ => x

@[scoped simp] theorem xco_some {W : WeierstrassCurve.Affine K} (x y : K) (h : W.Nonsingular x y) :
    xco (Point.some x y h) = x := rfl

theorem xco_neg {W : WeierstrassCurve.Affine K} (P : W.Point) : xco (-P) = xco P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.neg_some]; rfl

theorem eq_or_eq_neg_of_xco_eq {W : WeierstrassCurve.Affine K} {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : xco P = xco Q) : Q = P ∨ Q = -P := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd rfl hP
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hQ
  simp only [xco_some] at h
  subst h
  rcases Y_eq_of_X_eq h₂.left h₁.left rfl with hy | hy
  · left; subst hy; rfl
  · right
    rw [Point.neg_some]
    subst hy; rfl

section Count

variable {W : WeierstrassCurve.Affine K}

theorem nsmul_ne_zero_of_coprime (P : W.Point) {q : ℕ} (hq : 1 < q) (hP : addOrderOf P = q) {n : ℕ}
    (hn : q.Coprime n) : n • P ≠ 0 := by
  intro h0
  have h1 : addOrderOf (n • P) = q := by
    rw [← hP] at hn ⊢; exact hn.addOrderOf_nsmul
  rw [h0, addOrderOf_zero] at h1
  omega

theorem card_fibre_le_two (P : W.Point) {q : ℕ} (hq : 1 < q) (hP : addOrderOf P = q) (b : K) :
    (((Finset.range q).filter (fun n => q.Coprime n)).filter (fun n => xco (n • P) = b)).card ≤ 2 := by
  classical
  set S := ((Finset.range q).filter (fun n => q.Coprime n)).filter (fun n => xco (n • P) = b) with hS
  by_cases hne : S.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hne
    have hsub : S ⊆ ({n₀, q - n₀} : Finset ℕ) := by
      intro m hm
      have hm' := hm
      have hn₀' := hn₀
      simp only [hS, Finset.mem_filter, Finset.mem_range] at hm' hn₀'
      obtain ⟨⟨hmq, hmc⟩, hmb⟩ := hm'
      obtain ⟨⟨hn₀q, hn₀c⟩, hn₀b⟩ := hn₀'
      have hx : xco (n₀ • P) = xco (m • P) := by rw [hmb, hn₀b]
      rcases eq_or_eq_neg_of_xco_eq (nsmul_ne_zero_of_coprime P hq hP hn₀c)
        (nsmul_ne_zero_of_coprime P hq hP hmc) hx with heq | heq
      · have hmod : m ≡ n₀ [MOD addOrderOf P] := nsmul_eq_nsmul_iff_modEq.mp heq
        rw [hP] at hmod
        have : m = n₀ := by
          have := Nat.ModEq.eq_of_lt_of_lt hmod hmq hn₀q
          exact this
        simp [this]
      · have hsum : (m + n₀) • P = 0 := by rw [add_nsmul, heq, neg_add_cancel]
        have hdvd : q ∣ m + n₀ := by
          rw [← hP]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hsum
        obtain ⟨c, hc⟩ := hdvd
        have hc1 : c = 1 := by
          have h0 : 0 < m + n₀ := by
            rcases Nat.eq_zero_or_pos n₀ with h | h
            · subst h
              have : q = 1 := by simpa using hn₀c
              omega
            · omega
          have : c < 2 := by nlinarith
          have : 0 < c := by
            rcases Nat.eq_zero_or_pos c with h | h
            · subst h; omega
            · exact h
          omega
        subst hc1
        have : m = q - n₀ := by omega
        simp [this]
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

theorem totient_le_two_mul_card_image (P : W.Point) {q : ℕ} (hq : 1 < q) (hP : addOrderOf P = q) :
    q.totient ≤ 2 * (((Finset.range q).filter (fun n => q.Coprime n)).image (fun n => xco (n • P))).card := by
  classical
  rw [Nat.totient_eq_card_coprime]
  exact Finset.card_le_mul_card_image _ 2 (fun b _ => card_fibre_le_two P hq hP b)

end Count

section Unique

variable {W : WeierstrassCurve K}

theorem natDegree_eq_of_le_of_coeff_eq_one {h : K[X]} {d : ℕ} (h1 : h.natDegree ≤ d) (h2 : h.coeff d = 1) :
    h.natDegree = d :=
  le_antisymm h1 (le_natDegree_of_ne_zero (by rw [h2]; exact one_ne_zero))

theorem eq_prod_of_monic_of_roots (h : K[X]) (hm : h.Monic) (T : Finset K) (hT : ∀ t ∈ T, h.IsRoot t)
    (hdeg : h.natDegree ≤ T.card) : h = ∏ t ∈ T, (X - C t) := by
  classical
  have hdvd : (∏ t ∈ T, (X - C t)) ∣ h := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a _ b _ hab
      exact (pairwise_coprime_X_sub_C (s := fun t : K => t) (fun _ _ h => h)) hab
    · intro t ht
      exact dvd_iff_isRoot.mpr (hT t ht)
  have hmon : (∏ t ∈ T, (X - C t)).Monic := monic_prod_of_monic _ _ fun t _ => monic_X_sub_C t
  have hnat : (∏ t ∈ T, (X - C t)).natDegree = T.card := by
    rw [natDegree_prod_of_monic _ _ fun t _ => monic_X_sub_C t]
    simp
  exact eq_of_monic_of_dvd_of_natDegree_le hmon hm hdvd (by rw [hnat]; exact hdeg)

theorem cyclicGenKernel_unique {p k : ℕ} (hpk : 2 < p ^ k) {h₁ h₂ : K[X]}
    (hh₁ : W.IsCyclicGenKernel p k h₁) (hh₂ : W.IsCyclicGenKernel p k h₂)
    (P : W.toAffine.Point) (hP : addOrderOf P = p ^ k)
    (H₁ : ∀ n : ℕ, (p ^ k).Coprime n → h₁.IsRoot (xco (n • P)))
    (H₂ : ∀ n : ℕ, (p ^ k).Coprime n → h₂.IsRoot (xco (n • P))) : h₁ = h₂ := by
  classical
  set T := ((Finset.range (p ^ k)).filter (fun n => (p ^ k).Coprime n)).image (fun n => xco (n • P)) with hT
  have hcard : (p ^ k).totient ≤ 2 * T.card := totient_le_two_mul_card_image P (by omega) hP
  obtain ⟨e, he⟩ := Nat.totient_even hpk
  have hd : (p ^ k).totient / 2 ≤ T.card := by omega
  have hroots : ∀ (h : K[X]), (∀ n : ℕ, (p ^ k).Coprime n → h.IsRoot (xco (n • P))) → ∀ t ∈ T, h.IsRoot t := by
    intro h H t ht
    simp only [hT, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨n, ⟨-, hn⟩, rfl⟩ := ht
    exact H n hn
  have hdeg₁ := natDegree_eq_of_le_of_coeff_eq_one hh₁.natDegree_le hh₁.coeff_eq_one
  have hdeg₂ := natDegree_eq_of_le_of_coeff_eq_one hh₂.natDegree_le hh₂.coeff_eq_one
  rw [eq_prod_of_monic_of_roots h₁ (hh₁.monic W) T (hroots h₁ H₁) (by rw [hdeg₁]; exact hd),
    eq_prod_of_monic_of_roots h₂ (hh₂.monic W) T (hroots h₂ H₂) (by rw [hdeg₂]; exact hd)]

theorem twoKernel_unique {h₁ h₂ : K[X]} (hh₁ : W.IsTwoKernel h₁) (hh₂ : W.IsTwoKernel h₂) (a : K)
    (H₁ : h₁.IsRoot a) (H₂ : h₂.IsRoot a) : h₁ = h₂ := by
  have e₁ := eq_X_add_C_of_natDegree_le_one hh₁.natDegree_le
  have e₂ := eq_X_add_C_of_natDegree_le_one hh₂.natDegree_le
  rw [hh₁.coeff_eq_one, map_one, one_mul] at e₁
  rw [hh₂.coeff_eq_one, map_one, one_mul] at e₂
  have r₁ : h₁.coeff 0 = -a := by
    have := H₁; rw [e₁, IsRoot, eval_add, eval_X, eval_C] at this; linear_combination this
  have r₂ : h₂.coeff 0 = -a := by
    have := H₂; rw [e₂, IsRoot, eval_add, eval_X, eval_C] at this; linear_combination this
  rw [e₁, e₂, r₁, r₂]

theorem gamma0PowAt_unique {p k M : ℕ} (hp : p.Prime) (hk : 0 < k) (hM : M ≠ 0) (hdvd : p ^ k ∣ M) {h₁ h₂ : K[X]}
    (hh₁ : IsGamma0PowAt W p k h₁) (hh₂ : IsGamma0PowAt W p k h₂)
    (g : W.toAffine.Point) (hg : addOrderOf g = M)
    (H₁ : ∀ (n : ℕ) (x₁ y₁ : K) (hxy : W.toAffine.Nonsingular x₁ y₁),
      n • g = Point.some x₁ y₁ hxy → addOrderOf (n • g) = p ^ k → h₁.IsRoot x₁)
    (H₂ : ∀ (n : ℕ) (x₁ y₁ : K) (hxy : W.toAffine.Nonsingular x₁ y₁),
      n • g = Point.some x₁ y₁ hxy → addOrderOf (n • g) = p ^ k → h₂.IsRoot x₁) : h₁ = h₂ := by
  classical

  set P : W.toAffine.Point := (M / p ^ k) • g with hPdef
  have hP : addOrderOf P = p ^ k := by
    rw [hPdef, ← hg]
    exact addOrderOf_nsmul_addOrderOf_sub (by rw [hg]; exact hM) (by rw [hg]; exact hdvd)
  have hpk1 : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt

  have key : ∀ (h : K[X]), (∀ (n : ℕ) (x₁ y₁ : K) (hxy : W.toAffine.Nonsingular x₁ y₁),
      n • g = Point.some x₁ y₁ hxy → addOrderOf (n • g) = p ^ k → h.IsRoot x₁) →
      ∀ n : ℕ, (p ^ k).Coprime n → h.IsRoot (xco (n • P)) := by
    intro h H n hn
    have hord : addOrderOf (n • P) = p ^ k := by
      rw [← hP] at hn ⊢; exact hn.addOrderOf_nsmul
    have hne : n • P ≠ 0 := nsmul_ne_zero_of_coprime P hpk1 hP hn
    have hmul : n • P = (n * (M / p ^ k)) • g := by rw [hPdef, mul_nsmul']
    rcases hQ : n • P with _ | ⟨x₁, y₁, hxy⟩
    · exact absurd hQ hne
    · rw [xco_some]
      refine H (n * (M / p ^ k)) x₁ y₁ hxy (by rw [← hmul, hQ]) ?_
      rw [← hmul, hord]
  by_cases h2 : p ^ k = 2
  · rw [isGamma0PowAt_of_pow_eq_two W h2] at hh₁ hh₂
    have c1 : (p ^ k).Coprime 1 := Nat.coprime_one_right _
    have r₁ := key h₁ H₁ 1 c1
    have r₂ := key h₂ H₂ 1 c1
    exact twoKernel_unique hh₁ hh₂ _ r₁ r₂
  · rw [isGamma0PowAt_of_pow_ne_two W h2] at hh₁ hh₂
    have hpk : 2 < p ^ k := by omega
    exact cyclicGenKernel_unique hpk hh₁ hh₂ P hP (key h₁ H₁) (key h₂ H₂)

end Unique

section Transport

theorem isRoot_kernelVariableChangeDeg (C₀ : VariableChange K) (d : ℕ) (h : K[X]) {a : K} (ha : h.IsRoot a) :
    (kernelVariableChangeDeg C₀ d h).IsRoot (vcXInv C₀ a) := by
  have hu : ((C₀.u : Kˣ) : K) ≠ 0 := C₀.u.ne_zero
  have hin : ((Polynomial.C ((C₀.u : Kˣ) : K) ^ 2 * X + Polynomial.C C₀.r : K[X])).eval (vcXInv C₀ a) = a := by
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, vcXInv, Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [IsRoot] at ha ⊢
  rw [kernelVariableChangeDeg, eval_mul, eval_C, eval_comp, hin, ha, mul_zero]

noncomputable def vcInvHom (C₀ : VariableChange K) (W : WeierstrassCurve.Affine K) :
    W.Point →+ (C₀ • W).toAffine.Point where
  toFun := Point.vcInvFun C₀ W
  map_zero' := Point.vcInvFun_zero
  map_add' := Point.vcInvFun_add C₀ W

theorem vcInvHom_apply (C₀ : VariableChange K) (W : WeierstrassCurve.Affine K) (P : W.Point) :
    vcInvHom C₀ W P = Point.vcInvFun C₀ W P := rfl

theorem vcInvFun_injective (C₀ : VariableChange K) (W : WeierstrassCurve.Affine K) :
    Function.Injective (Point.vcInvFun C₀ W) :=
  (Point.vcFun_rightInverse (C := C₀) (W := W)).injective

theorem addOrderOf_vcInvFun (C₀ : VariableChange K) (W : WeierstrassCurve.Affine K) (P : W.Point) :
    addOrderOf (Point.vcInvFun C₀ W P) = addOrderOf P := by
  rw [← vcInvHom_apply]
  exact addOrderOf_injective (vcInvHom C₀ W) (vcInvFun_injective C₀ W) P

theorem vcInvFun_nsmul (C₀ : VariableChange K) (W : WeierstrassCurve.Affine K) (n : ℕ) (P : W.Point) :
    Point.vcInvFun C₀ W (n • P) = n • Point.vcInvFun C₀ W P := by
  rw [← vcInvHom_apply, map_nsmul]; rfl

theorem vcInvFun_some (C₀ : VariableChange K) (W : WeierstrassCurve.Affine K) (x y : K) (h : W.Nonsingular x y) :
    ∃ h', Point.vcInvFun C₀ W (Point.some x y h) = Point.some (vcXInv C₀ x) (vcYInv C₀ x y) h' :=
  ⟨_, rfl⟩

end Transport

end AlignSol
p2m_reactivate "P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_curve_eq_level_fst_eq_of_moduliPoint_mk_eq_of_raw_rigidDataH1Pow.AlignSol"

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel in
open scoped Classical in
theorem solution
    (A : Type) [CommRing A] (ℓg M' q : ℕ) [NeZero M']
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)
    (κ : Type) [Field κ] [IsAlgClosed κ] [DecidableEq κ] [Algebra A κ] (hM'κ : ((M' : ℕ) : κ) ≠ 0)
    (x x' : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw κ)
    (g : (x.curve).toAffine.Point) (g' : (x'.curve).toAffine.Point)
    (hg : (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : κ) (h₁ : (x.curve).toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (x.level.1 p).IsRoot x₁))
    (hg' : (addOrderOf g' = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : κ) (h₁ : (x'.curve).toAffine.Nonsingular x₁ y₁),
          n • g' = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g') = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (x'.level.1 p).IsRoot x₁))
    (heq : (Quot.mk _ (⟨x.curve, ⟨x.isUnit_Δ⟩, g, hg.1⟩ : ModularCurve.Gamma0Pair M' κ) : ModularCurve.ModuliPoint M' κ) =
      Quot.mk _ (⟨x'.curve, ⟨x'.isUnit_Δ⟩, g', hg'.1⟩ : ModularCurve.Gamma0Pair M' κ)) :
    ∃ C₀ : WeierstrassCurve.VariableChange κ,
      ((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C₀ x).curve = x'.curve ∧ ((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C₀ x).level.1 = x'.level.1 := by
  classical

  obtain ⟨γ, hγ, k, hk, hgg'⟩ := (ModularCurve.ModuliPoint.mk_eq_mk_iff_step _ _).mp heq
  refine ⟨γ, hγ, ?_⟩

  have hM0 : M' ≠ 0 := NeZero.ne M'
  obtain ⟨hgo, hgr⟩ := hg
  obtain ⟨hgo', hgr'⟩ := hg'
  obtain ⟨W', hΔ', lev', hlev'⟩ := x'
  dsimp only at hγ g' hgo' hgr' hgg' hlev' ⊢
  subst hγ
  have hgeq : g' = k • WeierstrassCurve.Affine.Point.vcInvFun γ x.curve.toAffine g := eq_of_heq hgg'
  funext p
  show ModularCurve.kernelVariableChangeDeg γ (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
      (x.level.1 p) = lev'.1 p
  clear heq hgg'
  have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
  have hkpos : 0 < M'.factorization (p : ℕ) :=
    hp.factorization_pos_of_dvd hM0 (Nat.dvd_of_mem_primeFactors p.2)
  have hdvd : (p : ℕ) ^ M'.factorization (p : ℕ) ∣ M' := Nat.ordProj_dvd M' _

  have hh₁ : IsGamma0PowAt (γ • x.curve) (p : ℕ) (M'.factorization (p : ℕ))
      (kernelVariableChangeDeg γ (gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (x.level.1 p)) :=
    hM κ x.curve γ (p : ℕ) (M'.factorization (p : ℕ)) (x.level.1 p) (x.isLevel.1.1 p)
  have hh₂ : IsGamma0PowAt (γ • x.curve) (p : ℕ) (M'.factorization (p : ℕ)) (lev'.1 p) := hlev'.1.1 p
  refine AlignSol.gamma0PowAt_unique hp hkpos hM0 hdvd hh₁ hh₂ g' hgo' ?_ (hgr' p)

  intro n x₁ y₁ hxy hn hord

  have htr : n • g' = WeierstrassCurve.Affine.Point.vcInvFun γ x.curve.toAffine ((n * k) • g) := by
    rw [hgeq, ← mul_nsmul', AlignSol.vcInvFun_nsmul]
  have hordQ : addOrderOf ((n * k) • g) = (p : ℕ) ^ M'.factorization (p : ℕ) := by
    have := hord
    rw [htr, AlignSol.addOrderOf_vcInvFun] at this
    exact this
  rcases hQ : (n * k) • g with _ | ⟨x₀, y₀, h₀⟩
  · exfalso
    rw [hQ] at htr
    have h0 : n • g' = 0 := by rw [htr]; rfl
    rw [h0] at hn
    exact WeierstrassCurve.Affine.Point.some_ne_zero hxy hn.symm
  · have hroot : (x.level.1 p).IsRoot x₀ := hgr p (n * k) x₀ y₀ h₀ hQ (by first | exact hordQ | (rw [hQ]; exact hordQ))
    obtain ⟨h', hsome⟩ := AlignSol.vcInvFun_some γ x.curve.toAffine x₀ y₀ h₀
    rw [hQ, hsome] at htr
    rw [htr] at hn
    have hx₁ : WeierstrassCurve.Affine.vcXInv γ x₀ = x₁ := by
      have := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hn
      exact this.1
    rw [← hx₁]
    exact AlignSol.isRoot_kernelVariableChangeDeg γ _ _ hroot

#print axioms solution

end S_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_curve_eq_level_fst_eq_of_moduliPoint_mk_eq_of_raw_rigidDataH1Pow
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_curve_eq_level_fst_eq_of_moduliPoint_mk_eq_of_raw_rigidDataH1Pow (solution)
