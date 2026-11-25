-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.tauFG_KTtoS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:36:16.953274+00:00
-- url     : https://prove2.me/submissions/fbe5679d-f5b6-4041-8abf-629b3ab1d3ce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply


section
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
private theorem tauFG_sH_X (c : ι) (b : Fin (d.D + 1)) (u : Kˣ) (v : TVar d.D d.N) :
    tauFG (Ω := Ω c) b u (d.sH c (X v)) = d.sH c (sigP b u (X v)) := by
  have hKC : ∀ r : K, algebraMap K (OmS (Ω c) d.D d.N) r =
      algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (C (algebraMap K (Ω c) r)) := by
    intro r
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)]
    rfl
  have hTC : ∀ a : Ω c, tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u (C a) = C a :=
    fun a => (tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u).commutes a
  have hconst : ∀ r : K, tauFG (Ω := Ω c) (D := d.D) (N := d.N) b u
      (algebraMap K (OmS (Ω c) d.D d.N) r) = algebraMap K (OmS (Ω c) d.D d.N) r := by
    intro r
    rw [hKC]
    unfold tauFG
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    congr 1
    exact hTC _
  have hTin : ∀ w : SVar d.D d.N, IsBaseBlockVar b w →
      tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u (X w) = C (algebraMap K (Ω c) u) * X w := by
    intro w hw
    show (aeval (R := Ω c) (S₁ := MvPolynomial (SVar d.D d.N) (Ω c)) _) (X w) = _
    rw [aeval_X]
    try dsimp only
    rw [if_pos hw]
    rfl
  have hTout : ∀ w : SVar d.D d.N, ¬ IsBaseBlockVar b w →
      tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u (X w) = X w := by
    intro w hw
    show (aeval (R := Ω c) (S₁ := MvPolynomial (SVar d.D d.N) (Ω c)) _) (X w) = _
    rw [aeval_X]
    try dsimp only
    rw [if_neg hw]
  have hsX : ∀ w : TVar d.D d.N, d.sH c (X w) = sImg (d.jc c) (d.x c) w := fun w => by
    show aeval (sImg (d.jc c) (d.x c)) (X w) = _
    exact aeval_X _ _
  have hsC : d.sH c (C (u : K)) = algebraMap K _ (u : K) := (d.sH c).commutes _
  have hX : ∀ v : TVar d.D d.N, tauFG (Ω := Ω c) b u (d.sH c (X v)) = d.sH c (sigP b u (X v)) := by
    rintro ⟨i, j⟩
    by_cases hib : i = b
    · have hs : sigP (K := K) (N := d.N) b u (X (i, j)) = C (u : K) * X (i, j) := by
        show (aeval (R := K) (S₁ := KTp K d.D d.N) _) (X (i, j)) = _
        rw [aeval_X]
        try dsimp only
        rw [if_pos hib]
      rw [hs, map_mul, hsC, hsX, hKC]
      unfold sImg tauFG
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, ← map_mul]
      congr 1
      show tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u _ = _
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · rw [show ∀ (A : MvPolynomial (SVar d.D d.N) (Ω c)) (F : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)),
            Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) A F (d.jc c) = A
            from fun A F => Fin.insertNth_apply_same _ _ _]
        split_ifs with hi0
        · exact hTin _ (hib.symm.trans hi0)
        · simp only [map_neg, map_sum, map_mul, hTC, fun k => hTin (Sum.inr (i, k)) hib, mul_neg,
            Finset.mul_sum, mul_assoc]
      · rw [show ∀ (A : MvPolynomial (SVar d.D d.N) (Ω c)) (F : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)),
            Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) A F
              ((d.jc c).succAbove k) = F k
            from fun A F => Fin.insertNth_apply_succAbove _ _ _ _]
        exact hTin _ hib
    · have hs : sigP (K := K) (N := d.N) b u (X (i, j)) = X (i, j) := by
        show (aeval (R := K) (S₁ := KTp K d.D d.N) _) (X (i, j)) = _
        rw [aeval_X]
        try dsimp only
        rw [if_neg hib]
      rw [hs, hsX]
      unfold sImg tauFG
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      congr 1
      show tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u _ = _
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · rw [show ∀ (A : MvPolynomial (SVar d.D d.N) (Ω c)) (F : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)),
            Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) A F (d.jc c) = A
            from fun A F => Fin.insertNth_apply_same _ _ _]
        split_ifs with hi0
        · exact hTout _ (fun hb0 => hib (hi0.trans hb0.symm))
        · simp only [map_neg, map_sum, map_mul, hTC, fun k => hTout (Sum.inr (i, k)) hib]
      · rw [show ∀ (A : MvPolynomial (SVar d.D d.N) (Ω c)) (F : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)),
            Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) A F
              ((d.jc c).succAbove k) = F k
            from fun A F => Fin.insertNth_apply_succAbove _ _ _ _]
        exact hTout _ hib
  exact hX v
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (u : Kˣ) (z : KTf K d.D d.N) :
    tauFG (Ω := Ω c) b u (d.KTtoS h c z) = d.KTtoS h c (sigF b u z) := by
  have hsH : ∀ q : KTp K d.D d.N, d.KTtoS h c (algebraMap _ (KTf K d.D d.N) q) = d.sH c q := by
    intro q
    unfold KTtoS
    exact IsFractionRing.lift_algebraMap _ _
  have hKC : ∀ r : K, algebraMap K (OmS (Ω c) d.D d.N) r =
      algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (C (algebraMap K (Ω c) r)) := by
    intro r
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)]
    rfl
  have hTC : ∀ a : Ω c, tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u (C a) = C a :=
    fun a => (tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u).commutes a
  have hconst : ∀ r : K, tauFG (Ω := Ω c) (D := d.D) (N := d.N) b u
      (algebraMap K (OmS (Ω c) d.D d.N) r) = algebraMap K (OmS (Ω c) d.D d.N) r := by
    intro r
    rw [hKC]
    unfold tauFG
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    congr 1
    exact hTC _
  have hTin : ∀ w : SVar d.D d.N, IsBaseBlockVar b w →
      tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u (X w) = C (algebraMap K (Ω c) u) * X w := by
    intro w hw
    show (aeval (R := Ω c) (S₁ := MvPolynomial (SVar d.D d.N) (Ω c)) _) (X w) = _
    rw [aeval_X]
    try dsimp only
    rw [if_pos hw]
    rfl
  have hTout : ∀ w : SVar d.D d.N, ¬ IsBaseBlockVar b w →
      tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u (X w) = X w := by
    intro w hw
    show (aeval (R := Ω c) (S₁ := MvPolynomial (SVar d.D d.N) (Ω c)) _) (X w) = _
    rw [aeval_X]
    try dsimp only
    rw [if_neg hw]
  have hsX : ∀ w : TVar d.D d.N, d.sH c (X w) = sImg (d.jc c) (d.x c) w := fun w => by
    show aeval (sImg (d.jc c) (d.x c)) (X w) = _
    exact aeval_X _ _
  have hsC : d.sH c (C (u : K)) = algebraMap K _ (u : K) := (d.sH c).commutes _
  have hX : ∀ v : TVar d.D d.N, tauFG (Ω := Ω c) b u (d.sH c (X v)) = d.sH c (sigP b u (X v)) :=
    fun v => tauFG_sH_X d c b u v
  have hpoly : ∀ q : KTp K d.D d.N, tauFG (Ω := Ω c) b u (d.sH c q) = d.sH c (sigP b u q) := by
    intro q
    have e := MvPolynomial.ringHom_ext
      (f := (tauFG (Ω := Ω c) (D := d.D) (N := d.N) b u).toRingHom.comp (d.sH c).toRingHom)
      (g := (d.sH c).toRingHom.comp (sigP (K := K) (N := d.N) b u).toRingEquiv.toRingHom)
      (fun r => by
        show tauFG (Ω := Ω c) b u (d.sH c (C r)) = d.sH c (sigP b u (C r))
        rw [show sigP (K := K) (N := d.N) b u (C r) = C r from (sigP (K := K) (N := d.N) b u).commutes r,
          show d.sH c (C r) = algebraMap K _ r from (d.sH c).commutes r, hconst])
      (fun v => hX v)
    exact RingHom.congr_fun e q
  have hsig : ∀ g : KTp K d.D d.N, sigF (K := K) (D := d.D) (N := d.N) b u
      (algebraMap _ (KTf K d.D d.N) g) = algebraMap _ (KTf K d.D d.N) (sigP b u g) := fun g => by
    unfold sigF
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ g
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := KTp K d.D d.N) z
  simp only [map_div₀, hsH, hsig, hpoly]
end ReciprocityTheory.ChartRestriction.G.T0.Data
