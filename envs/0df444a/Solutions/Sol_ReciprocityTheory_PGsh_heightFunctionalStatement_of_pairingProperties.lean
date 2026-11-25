-- Prove2me | solution 1 for ReciprocityTheory.PGsh.heightFunctionalStatement_of_pairingProperties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:09:31.589813+00:00
-- url     : https://prove2.me/submissions/8a79502a-5549-410d-893f-07aac5a69939

import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
import Definitions.Def_ReciprocityTheory_DualLattices_ToSigmaAddFstZeroFst
import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
import Theorems.Thm_ReciprocityTheory_PGsh_DualPair_isFibreSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace BX
variable {B : BX R₀}
private lemma tot_eq_of_heq {R : LAlg R₀} {x y x' y' : B.G R} (u : B.P R x y) (u' : B.P R x' y')
    (hx : x = x') (hy : y = y') (h : HEq u u') : B.tot u = B.tot u' := by
  subst hx
  subst hy
  rw [eq_of_heq h]
private lemma heq_of_tot_eq {R : LAlg R₀} {x y x' y' : B.G R} (u : B.P R x y)
    (u' : B.P R x' y') (h : B.tot u = B.tot u') : HEq u u' := by
  have h' : (⟨x, y, u⟩ : Σ x y : B.G R, B.P R x y) = ⟨x', y', u'⟩ := h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h'
  obtain ⟨rfl, h3⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  exact h3
private lemma tot_pmap_comp' {R S T : LAlg R₀} (f : LHom R S) (g : LHom S T) {x y : B.G R}
    (u : B.P R x y) : B.tot (B.pmap (g.comp f) u) = B.tot (B.pmap g (B.pmap f u)) :=
  tot_eq_of_heq _ _ (B.map_comp f g x) (B.map_comp f g y) (B.pmap_comp f g u)
private lemma dualPair_pi_comp_sigma {R : LAlg R₀} (Dp : DualPair R) : Dp.π.comp Dp.σ = LHom.id R :=
  Subtype.ext (AlgHom.ext fun r => Dp.sect r)
private lemma map_pi_map_sigma {R : LAlg R₀} (Dp : DualPair R) (y : B.G R) :
    B.map Dp.π (B.map Dp.σ y) = y := by
  rw [← B.map_comp, dualPair_pi_comp_sigma, B.map_id]
private lemma zσ {R : LAlg R₀} (Dp : DualPair R) (y : B.G R) {x : B.G Dp.D}
    (c : B.P Dp.D x (B.map Dp.σ y)) (hc : B.tot (B.pmap Dp.π c) = B.tot (B.zero1 y)) :
    B.tot (B.pmap (Dp.σ.comp Dp.π) c) = B.tot (B.zero1 (B.map Dp.σ y)) := by
  rw [tot_pmap_comp']
  have e : B.tot (B.pmap Dp.σ (B.pmap Dp.π c)) = B.tmap Dp.σ (B.tot (B.pmap Dp.π c)) := rfl
  rw [e, hc]
  exact tot_eq_of_heq _ _ (map_zero (B.map Dp.σ)) rfl (B.zeroFst_nat Dp.σ y)
private lemma dualPair_muL_zero {R : LAlg R₀} (Dp : DualPair R) : Dp.μL 0 = Dp.σ.comp Dp.π :=
  Subtype.ext (AlgHom.ext fun a => by
    show Dp.fμ 0 a = Dp.σ.1 (Dp.π.1 a)
    simp [DualPair.fμ])
private lemma tot_pmap_id' {R : LAlg R₀} {x y : B.G R} (u : B.P R x y) :
    B.tot (B.pmap (LHom.id R) u) = B.tot u :=
  tot_eq_of_heq _ _ (B.map_id R x) (B.map_id R y) (B.pmap_id u)
private lemma tot_add1_congr {R : LAlg R₀} {x₁ x₂ y x₁' x₂' y' : B.G R} {u₁ : B.P R x₁ y}
    {u₂ : B.P R x₂ y} {u₁' : B.P R x₁' y'} {u₂' : B.P R x₂' y'} (h₁ : B.tot u₁ = B.tot u₁')
    (h₂ : B.tot u₂ = B.tot u₂') : B.tot (B.add1 u₁ u₂) = B.tot (B.add1 u₁' u₂') := by
  have ex₁ : x₁ = x₁' := congrArg Sigma.fst h₁
  have ey : y = y' := congrArg (fun t : (Σ x y : B.G R, B.P R x y) => t.2.1) h₁
  have ex₂ : x₂ = x₂' := congrArg Sigma.fst h₂
  subst ex₁
  subst ey
  subst ex₂
  rw [eq_of_heq (heq_of_tot_eq _ _ h₁), eq_of_heq (heq_of_tot_eq _ _ h₂)]
private lemma tot_pmap_add1 {R S : LAlg R₀} (f : LHom R S) {x x' y : B.G R}
    (u : B.P R x y) (u' : B.P R x' y) :
    B.tot (B.pmap f (B.add1 u u')) = B.tot (B.add1 (B.pmap f u) (B.pmap f u')) :=
  tot_eq_of_heq _ _ (map_add (B.map f) x x') rfl (B.addFst_nat f u u')
private lemma tot_pmap_tr2 {R S : LAlg R₀} (f : LHom R S) {x y y' : B.G R} (h : y = y')
    (u : B.P R x y) : B.tot (B.pmap f (B.tr2 h u)) = B.tot (B.pmap f u) := by
  subst h
  rfl
private lemma tot_add1_zero1_right {R : LAlg R₀} {x y : B.G R} (u : B.P R x y) :
    B.tot (B.add1 u (B.zero1 y)) = B.tot u :=
  (tot_eq_of_heq _ _ (add_comm x 0) rfl (B.addFst_comm u (B.zero1 y))).trans
    (tot_eq_of_heq _ _ (zero_add x) rfl (B.zeroFst_add u))
private lemma tot_add1_zero1_left {R : LAlg R₀} {x y : B.G R} (u : B.P R x y) :
    B.tot (B.add1 (B.zero1 y) u) = B.tot u :=
  tot_eq_of_heq _ _ (zero_add x) rfl (B.zeroFst_add u)
private lemma dualPair_muL_one {R : LAlg R₀} (Dp : DualPair R) : Dp.μL 1 = LHom.id Dp.D :=
  Subtype.ext (AlgHom.ext fun a => by
    show Dp.fμ 1 a = a
    simp [DualPair.fμ])
private lemma dualPair_exists_lhom_mu_pair {R : LAlg R₀} (Dp : DualPair R) (c c' : (R : Type u)) :
    ∃ k : LHom Dp.D Dp.F, Dp.p₁L.comp k = Dp.μL c ∧ Dp.p₂L.comp k = Dp.μL c' ∧
      Dp.sL.comp k = Dp.μL (c + c') ∧
      ∀ r, ((k.1 (Dp.σ.1 r) : Dp.fpS) : Prod (Dp.D : Type u) (Dp.D : Type u)) =
        (Dp.σ.1 r, Dp.σ.1 r) := by
  have hmem : ∀ d, (Dp.μA c d, Dp.μA c' d) ∈ Dp.fpS := fun d => by
    show Dp.π.1 (Dp.μA c d) = Dp.π.1 (Dp.μA c' d)
    rw [Dp.π_μA, Dp.π_μA]
  refine ⟨mkLHom (AlgHom.codRestrict ((Dp.μA c).prod (Dp.μA c')) Dp.fpS hmem) fun a ha =>
    Dp.isUnit_of_π ?_, ?_, ?_, ?_, ?_⟩
  · have h := (ha.map ((AlgHom.fst R₀ _ _).comp Dp.fpS.val)).map Dp.π.1
    rw [← Dp.π_μA c a]
    exact h
  · exact Subtype.ext (AlgHom.ext fun d => rfl)
  · exact Subtype.ext (AlgHom.ext fun d => rfl)
  · refine Subtype.ext (AlgHom.ext fun d => ?_)
    show Dp.fμ c d + Dp.fμ c' d - Dp.σ.1 (Dp.π.1 (Dp.fμ c d)) = Dp.fμ (c + c') d
    simp only [DualPair.fμ, map_add, map_mul, map_sub, Dp.sect]
    ring
  · intro r
    show (Dp.fμ c (Dp.σ.1 r), Dp.fμ c' (Dp.σ.1 r)) = (Dp.σ.1 r, Dp.σ.1 r)
    simp [DualPair.fμ, Dp.sect]
private lemma tot_tr1 {R : LAlg R₀} {x x' y : B.G R} (h : x = x') (u : B.P R x y) :
    B.tot (B.tr1 h u) = B.tot u := by
  subst h
  rfl
private lemma eh {R : LAlg R₀} (Dp : DualPair R) (y : B.G R) {x₁ x₂ : B.G Dp.D}
    (a : B.P Dp.D x₁ (B.map Dp.σ y)) (b : B.P Dp.D x₂ (B.map Dp.σ y))
    (ha : B.tot (B.pmap Dp.π a) = B.tot (B.zero1 y))
    (hb : B.tot (B.pmap Dp.π b) = B.tot (B.zero1 y))
    (w : Σ x y : B.G Dp.F, B.P Dp.F x y) (hw1 : B.tmap Dp.p₁L w = B.tot a)
    (hw2 : B.tmap Dp.p₂L w = B.tot b) : B.tmap Dp.sL w = B.tot (B.add1 a b) := by
  obtain ⟨j₁, h11, h12, h1s, h1σ⟩ := dualPair_exists_lhom_mu_pair Dp 1 0
  obtain ⟨j₂, h21, h22, h2s, h2σ⟩ := dualPair_exists_lhom_mu_pair Dp 0 1
  rw [dualPair_muL_one] at h11 h22
  rw [dualPair_muL_zero] at h12 h21
  rw [add_zero, dualPair_muL_one] at h1s
  rw [zero_add, dualPair_muL_one] at h2s
  have hjσ : j₁.comp Dp.σ = j₂.comp Dp.σ :=
    Subtype.ext (AlgHom.ext fun r => Subtype.ext ((h1σ r).trans (h2σ r).symm))
  have e : B.map j₁ (B.map Dp.σ y) = B.map j₂ (B.map Dp.σ y) := by
    rw [← B.map_comp, ← B.map_comp, hjσ]
  obtain ⟨t, ht⟩ : ∃ t, t = B.add1 (B.pmap j₁ a) (B.tr2 e.symm (B.pmap j₂ b)) := ⟨_, rfl⟩
  have hA : B.tot (B.pmap Dp.p₁L t) = B.tot a := by
    rw [ht, tot_pmap_add1]
    have e1 : B.tot (B.pmap Dp.p₁L (B.pmap j₁ a)) = B.tot a := by
      rw [← tot_pmap_comp', h11, tot_pmap_id']
    have e2 : B.tot (B.pmap Dp.p₁L (B.tr2 e.symm (B.pmap j₂ b))) =
        B.tot (B.zero1 (B.map Dp.σ y)) := by
      rw [tot_pmap_tr2, ← tot_pmap_comp', h21]
      exact zσ Dp y b hb
    rw [tot_add1_congr e1 e2, tot_add1_zero1_right]
  have hB : B.tot (B.pmap Dp.p₂L t) = B.tot b := by
    rw [ht, tot_pmap_add1]
    have e1 : B.tot (B.pmap Dp.p₂L (B.pmap j₁ a)) = B.tot (B.zero1 (B.map Dp.σ y)) := by
      rw [← tot_pmap_comp', h12]
      exact zσ Dp y a ha
    have e2 : B.tot (B.pmap Dp.p₂L (B.tr2 e.symm (B.pmap j₂ b))) = B.tot b := by
      rw [tot_pmap_tr2, ← tot_pmap_comp', h22, tot_pmap_id']
    rw [tot_add1_congr e1 e2, tot_add1_zero1_left]
  obtain ⟨c, -, huniq⟩ := B.fibre_P Dp.p₁L Dp.p₂L Dp.π Dp.π Dp.isFibreSq (B.tot a) (B.tot b)
    (by
      show B.tot (B.pmap Dp.π a) = B.tot (B.pmap Dp.π b)
      rw [ha, hb])
  have hw : w = c := huniq w ⟨hw1, hw2⟩
  have htc : B.tot t = c := huniq (B.tot t) ⟨hA, hB⟩
  rw [hw, ← htc]
  show B.tot (B.pmap Dp.sL t) = _
  rw [ht, tot_pmap_add1]
  have e3 : B.tot (B.pmap Dp.sL (B.pmap j₁ a)) = B.tot a := by
    rw [← tot_pmap_comp', h1s, tot_pmap_id']
  have e4 : B.tot (B.pmap Dp.sL (B.tr2 e.symm (B.pmap j₂ b))) = B.tot b := by
    rw [tot_pmap_tr2, ← tot_pmap_comp', h2s, tot_pmap_id']
  exact tot_add1_congr e3 e4
private lemma nsmul1_tot {R : LAlg R₀} (Dp : DualPair R) (y : B.G R) {x : B.G Dp.D}
    (u : B.P Dp.D x (B.map Dp.σ y)) (hu : B.tot (B.pmap Dp.π u) = B.tot (B.zero1 y)) (n : ℕ) :
    B.tot (B.nsmul1 u n) = B.tot (B.pmap (Dp.μL (n : (R : Type u))) u) := by
  have hπμ : ∀ c, Dp.π.comp (Dp.μL c) = Dp.π := fun c =>
    Subtype.ext (AlgHom.ext fun d => Dp.π_μA c d)
  induction n with
  | zero =>
    show B.tot (B.tr1 _ (B.zero1 (B.map Dp.σ y))) = _
    rw [tot_tr1, Nat.cast_zero, dualPair_muL_zero]
    exact (zσ Dp y u hu).symm
  | succ n ih =>
    obtain ⟨k, hk1, hk2, hks, -⟩ := dualPair_exists_lhom_mu_pair Dp (n : (R : Type u)) 1
    rw [dualPair_muL_one] at hk2
    have ha : B.tot (B.pmap Dp.π (B.nsmul1 u n)) = B.tot (B.zero1 y) := by
      have e : B.tot (B.pmap Dp.π (B.nsmul1 u n)) = B.tmap Dp.π (B.tot (B.nsmul1 u n)) := rfl
      rw [e, ih]
      show B.tot (B.pmap Dp.π (B.pmap (Dp.μL (n : (R : Type u))) u)) = _
      rw [← tot_pmap_comp', hπμ]
      exact hu
    have key := eh Dp y (B.nsmul1 u n) u ha hu (B.tot (B.pmap k u))
      (by
        show B.tot (B.pmap Dp.p₁L (B.pmap k u)) = _
        rw [← tot_pmap_comp', hk1]
        exact ih.symm)
      (by
        show B.tot (B.pmap Dp.p₂L (B.pmap k u)) = _
        rw [← tot_pmap_comp', hk2, tot_pmap_id'])
    show B.tot (B.tr1 _ (B.add1 (B.nsmul1 u n) u)) = _
    rw [tot_tr1, ← key, Nat.cast_succ, ← hks]
    exact (tot_pmap_comp' k Dp.sL u).symm
private lemma part_a {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (hN : (N : (R : Type u)) = 0)
    (y : B.G R) (v : B.gg) (u : B.P Dp.D (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) (B.map Dp.σ y))
    (hu : HEq (B.pmap Dp.π u) (B.zero1 y)) : HEq (B.nsmul1 u N) (B.zero1 (B.map Dp.σ y)) := by
  have hx : B.map Dp.π (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) = 0 :=
    (B.tg_ker Dp.π Dp.sqZero _).mpr ⟨_, rfl⟩
  have hu' : B.tot (B.pmap Dp.π u) = B.tot (B.zero1 y) :=
    tot_eq_of_heq _ _ hx (map_pi_map_sigma Dp y) hu
  apply heq_of_tot_eq
  rw [nsmul1_tot Dp y u hu' N]
  have hμ : Dp.μL ((N : ℕ) : (R : Type u)) = Dp.σ.comp Dp.π := by
    rw [hN]
    exact dualPair_muL_zero Dp
  rw [hμ]
  exact zσ Dp y u hu'
private lemma part_b (h1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) :
    ∃! h : B.gg →ₗ[R₀] (R : Type u), B.IsHeight Dp N y h := by
  refine ⟨hgt h1 Dp N hN y hy, fun v => cf_spec h1 Dp N hN y hy v, fun h' hh' => ?_⟩
  ext v
  obtain ⟨z, hz, ez⟩ := hh' v
  obtain ⟨z0, hz0, ez0⟩ := cf_spec h1 Dp N hN y hy v
  exact c_unique h1 Dp N _ _ _ _ z z0 hz hz0 ez ez0
private lemma part_c (h1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (y y' : B.G R) (h h' : B.gg →ₗ[R₀] (R : Type u)) (hh : B.IsHeight Dp N y h)
    (hh' : B.IsHeight Dp N y' h') : B.IsHeight Dp N (y + y') (h + h') := by
  intro v
  obtain ⟨z, hz, ez⟩ := hh v
  obtain ⟨z', hz', ez'⟩ := hh' v
  obtain ⟨hx, hy1, -⟩ := id hz
  obtain ⟨-, hy2, -⟩ := id hz'
  obtain ⟨w, hw⟩ := h1.1 Dp.D N _ (B.map Dp.σ y + B.map Dp.σ y') hx
    (by rw [nsmul_add, hy1, hy2, add_zero])
  have hwz := h1.2.2.2.1 Dp.D N _ _ _ z z' w hz hz' hw
  refine ⟨w, by rw [map_add]; exact hw, ?_⟩
  rw [hwz, Units.val_mul, ez, ez', LinearMap.add_apply, map_add]
  linear_combination (Dp.σ.1 (h v) * Dp.σ.1 (h' v)) * Dp.η_sq
end BX
end ReciprocityTheory.PGsh
end
end

set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (B : BX R₀) (h1 : PairingPropertiesStatement B) : HighestWeightVectorUniformBounds B := by
  intro R Dp N hN
  exact ⟨fun y v u hu => BX.part_a Dp N hN y v u hu, fun y hy => BX.part_b h1 Dp N hN y hy,
    fun y y' h h' hh hh' => BX.part_c h1 Dp N y y' h h' hh hh'⟩
end ReciprocityTheory.PGsh
