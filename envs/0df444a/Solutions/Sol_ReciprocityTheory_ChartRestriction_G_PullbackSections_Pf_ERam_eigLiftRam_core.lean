-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.eigLiftRam_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:56:12.086324+00:00
-- url     : https://prove2.me/submissions/f54fb962-1e2e-4130-94ad-530aeb315bca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_actP_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_actP_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_actP_fst_eig
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_hset_snd_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_betaH_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_betaH_sub_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_actP_eig
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_beta_vanish
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_evD_orth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_OactH_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_hset_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_hset_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_eigen_orthogonality


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [Field k] [Algebra ℚ k] [Algebra R k]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution (hRQ : IsRQ (R := R) k) (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h)
    {L Ty Pl π : Type} [Fintype Ty] (ty : L → Ty) (χ : Ty → O →+* k) (cjT : Ty → Ty)
    (hχsep : ∀ t t', t' ≠ cjT t → ∃ a, χ t a ≠ χ t' (star a)) (hχinj : ∀ t t', t ≠ t' → ∃ a, χ t a ≠ χ t' a)
    (u : L → Fin d → R)
    (heig : ∀ ℓ a, (dAct k B a).mulVec (fun i => algebraMap R k (u ℓ i)) = χ (ty ℓ) a • fun i => algebraMap R k (u ℓ i))
    (nt : Ty → ℕ) (bt : ∀ t, Fin (nt t) → O) (ct : ∀ t, Fin (nt t) → k) (heqt : ∀ t, IsEqv (χ t) (bt t) (ct t))
    (hcompH : ∑ t, actD (EigA.dActH k B) (bt t) (ct t) = 1) (hcompS : ∑ t, actD (EigA.dActS k B) (bt t) (ct t) = 1)
    (pl : Ty → Pl) (cjP : Pl → Pl) (hpl : ∀ t, pl (cjT t) = cjP (pl t))
    (nP : Pl → ℕ) (bP : ∀ w, Fin (nP w) → O) (aP : ∀ w, Fin (nP w) → R)
    (hP : ∀ w t, evD (χ t) (bP w) (fun i => algebraMap R k (aP w i)) = if pl t = w then 1 else 0)
    (nE : Ty → ℕ) (bE : ∀ t, Fin (nE t) → O) (cE : ∀ t, Fin (nE t) → k) (heqE : ∀ t, IsEqv (χ t) (bE t) (cE t))
    (hnE : ∀ t, evD (χ t) (bE t) (cE t) = 1) (r : Ty → R)
    (hr : ∀ t i, ∃ v : R, algebraMap R k v = algebraMap R k (r t) * cE t i)
    (c : Ty → π) (s : Ty → Bool) (hpair : ∀ t t', pl t' = cjP (pl t) → c t = c t' ∧ s t ≠ s t') :
    ∃ (φ : L → Fin d → R) (ψ : L → Fin d → k),
      (∀ ℓ i, algebraMap R k (r (ty ℓ)) * ψ ℓ i ∈ (algebraMap R k).range) ∧
      (∀ ℓ ℓ', ty ℓ' ≠ cjT (ty ℓ) →
        ∑ i, (algebraMap R k (φ ℓ' i) + ψ ℓ' i - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
          algebraMap R k (u ℓ i) = 0) ∧
      OppositePairVanishing k (fun ℓ => c (ty ℓ)) (fun ℓ => s (ty ℓ))
        (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
          fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
        (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
          fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)) ∧
      OppositePairVanishing k (fun ℓ => c (ty ℓ)) (fun ℓ => s (ty ℓ)) (fun ℓ => (0, ψ ℓ))
        (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
          fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)) ∧
      OppositePairVanishing k (fun ℓ => c (ty ℓ)) (fun ℓ => s (ty ℓ))
        (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
          fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
        (fun ℓ => (0, ψ ℓ)) := by
  classical
  have hinj : Function.Injective (algebraMap R k) := hRQ.1

  have hξ0 : ∀ ℓ, ((fun j => algebraMap R k (u ℓ j)), -(sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j))) ∈
      Hset (R := R) k h := fun ℓ => ⟨u ℓ, 0, Prod.ext rfl (by funext i; simp)⟩
  let ξh : L → (Fin d → k) × (Fin d → k) := fun ℓ => actP B (bP (pl (ty ℓ))) (fun i => algebraMap R k (aP (pl (ty ℓ)) i))
    ((fun j => algebraMap R k (u ℓ j)), -(sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)))
  have hξh_mem : ∀ ℓ, ξh ℓ ∈ Hset (R := R) k h := fun ℓ => actP_mem hRQ B h hc _ _ (hξ0 ℓ)
  have hξh_fst : ∀ ℓ, (ξh ℓ).1 = fun j => algebraMap R k (u ℓ j) := by
    intro ℓ
    show (actP B _ _ _).1 = _
    rw [actP_fst_eig B (χ (ty ℓ)) _ _ _ (heig ℓ), hP, if_pos rfl, one_smul]
  choose u1 φ1 hu1 using hξh_mem
  have hU1 : ∀ ℓ, (fun j => algebraMap R k (u1 ℓ j)) = fun j => algebraMap R k (u ℓ j) := fun ℓ =>
    (congrArg Prod.fst (hu1 ℓ)).symm.trans (hξh_fst ℓ)
  have hξh_eq : ∀ ℓ, ξh ℓ = ((fun j => algebraMap R k (u ℓ j)),
      fun i => algebraMap R k (φ1 ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i) := by
    intro ℓ
    rw [hu1 ℓ, hU1 ℓ]

  let ξ : L → (Fin d → k) × (Fin d → k) := fun ℓ => actP B (bE (ty ℓ)) (cE (ty ℓ)) (ξh ℓ)
  have heigh : ∀ ℓ a, (dAct k B a).mulVec (ξh ℓ).1 = χ (ty ℓ) a • (ξh ℓ).1 := fun ℓ a => by
    rw [hξh_fst]; exact heig ℓ a
  have hξ_fst : ∀ ℓ, (ξ ℓ).1 = fun j => algebraMap R k (u ℓ j) := by
    intro ℓ
    show (actP B _ _ _).1 = _
    rw [actP_fst_eig B (χ (ty ℓ)) _ _ _ (heigh ℓ), hnE, one_smul, hξh_fst]
  let ψ : L → Fin d → k := fun ℓ i => (ξ ℓ).2 i - (ξh ℓ).2 i
  have hdiff : ∀ ℓ, ξ ℓ - ξh ℓ = ((0 : Fin d → k), ψ ℓ) := by
    intro ℓ
    refine Prod.ext ?_ rfl
    rw [Prod.fst_sub, hξ_fst, hξh_fst, sub_self]

  have hsuppP : ∀ w t, evD (χ t) (bP w) (fun i => algebraMap R k (aP w i)) ≠ 0 → pl t = w := by
    intro w t ht
    rw [hP] at ht
    by_contra hne
    exact ht (if_neg hne)
  have hsuppE : ∀ τ t, evD (χ t) (bE τ) (cE τ) ≠ 0 → pl t = pl τ := by
    intro τ t ht
    by_cases he : t = τ
    · rw [he]
    · obtain ⟨a, ha⟩ := hχinj t τ he
      exact absurd (evD_orth (χ τ) (χ t) (bE τ) (cE τ) (heqE τ) a ha) ht
  have hvan : ∀ {n n' : ℕ} (bz : Fin n → O) (cz : Fin n → k) (bw : Fin n' → O) (cw : Fin n' → k)
      (X Y : (Fin d → k) × (Fin d → k)) (l l' : L), ¬ (c (ty l) = c (ty l') ∧ s (ty l) ≠ s (ty l')) →
      (∀ t, evD (χ t) bz cz ≠ 0 → pl t = pl (ty l)) → (∀ t', evD (χ t') bw cw ≠ 0 → pl t' = pl (ty l')) →
      betaH k (actP B bz cz X) (actP B bw cw Y) = 0 := by
    intro n n' bz cz bw cw X Y l l' hnot hs1 hs2
    refine beta_vanish B χ nt bt ct heqt hcompH hcompS bz cz bw cw X Y fun t t' h1 h2 => ?_
    by_cases ht : t' = cjT t
    · exfalso
      apply hnot
      apply hpair
      rw [← hs2 t' h2, ht, hpl, hs1 t h1]
    · exact hχsep t t' ht
  have hA : ∀ l l', ¬ (c (ty l) = c (ty l') ∧ s (ty l) ≠ s (ty l')) → betaH k (ξh l) (ξh l') = 0 :=
    fun l l' hnot => hvan _ _ _ _ _ _ l l' hnot (hsuppP _) (hsuppP _)
  have hB : ∀ l l', ¬ (c (ty l) = c (ty l') ∧ s (ty l) ≠ s (ty l')) → betaH k (ξ l) (ξh l') = 0 :=
    fun l l' hnot => hvan _ _ _ _ _ _ l l' hnot (hsuppE _) (hsuppP _)
  have hC : ∀ l l', ¬ (c (ty l) = c (ty l') ∧ s (ty l) ≠ s (ty l')) → betaH k (ξh l) (ξ l') = 0 :=
    fun l l' hnot => hvan _ _ _ _ _ _ l l' hnot (hsuppP _) (hsuppE _)
  refine ⟨φ1, ψ, fun ℓ i => ?_, fun ℓ ℓ' hne => ?_, fun l l' hnot => ?_, fun l l' hnot => ?_, fun l l' hnot => ?_⟩
  ·
    choose v hv using hr (ty ℓ)
    have hrξ : algebraMap R k (r (ty ℓ)) • ξ ℓ ∈ Hset (R := R) k h := by
      show algebraMap R k (r (ty ℓ)) • actP B _ _ _ ∈ _
      rw [actP_smul]
      have e : (fun i => algebraMap R k (r (ty ℓ)) * cE (ty ℓ) i) = fun i => algebraMap R k (v i) :=
        funext fun i => (hv i).symm
      rw [e]
      exact actP_mem hRQ B h hc _ _ (hu1 ℓ ▸ ⟨u1 ℓ, φ1 ℓ, rfl⟩)
    have hrξh : algebraMap R k (-1) • (algebraMap R k (r (ty ℓ)) • ξh ℓ) ∈ Hset (R := R) k h :=
      EigA.hset_smul k h (-1) (EigA.hset_smul k h (r (ty ℓ)) (hu1 ℓ ▸ ⟨u1 ℓ, φ1 ℓ, rfl⟩))
    have hsum := EigA.hset_add k h hrξ hrξh
    have e2 : algebraMap R k (r (ty ℓ)) • ξ ℓ + algebraMap R k (-1) • (algebraMap R k (r (ty ℓ)) • ξh ℓ) =
        ((0 : Fin d → k), fun i => algebraMap R k (r (ty ℓ)) * ψ ℓ i) := by
      rw [map_neg, map_one, neg_one_smul, ← sub_eq_add_neg, ← smul_sub, hdiff]
      refine Prod.ext ?_ ?_
      · simp
      · funext i
        simp [Algebra.smul_def]
    rw [e2] at hsum
    exact hset_snd_int hsum hinj i
  ·
    obtain ⟨a, ha⟩ := hχsep (ty ℓ) (ty ℓ') hne
    have hv1 : ∀ b : O, OactH k B b ((fun j => algebraMap R k (u ℓ j)), (0 : Fin d → k)) =
        χ (ty ℓ) b • ((fun j => algebraMap R k (u ℓ j)), (0 : Fin d → k)) := by
      intro b
      rw [EigA.OactH_eq]
      refine Prod.ext (heig ℓ b) ?_
      simp
    have hβ := eigen_orthogonality R d O k B (χ (ty ℓ)) (χ (ty ℓ')) _ (ξ ℓ') hv1
      (fun b => actP_eig B (χ (ty ℓ')) _ _ (heqE (ty ℓ')) (ξh ℓ') b)
      ⟨a, isUnit_iff_ne_zero.2 (sub_ne_zero.2 ha)⟩
    simp only [betaH, Pi.zero_apply, zero_mul, sub_zero] at hβ
    have e3 : ∀ i, (ξ ℓ').2 i = algebraMap R k (φ1 ℓ' i) + ψ ℓ' i -
        (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i := by
      intro i
      show (ξ ℓ').2 i = algebraMap R k (φ1 ℓ' i) + ((ξ ℓ').2 i - (ξh ℓ').2 i) -
        (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i
      rw [hξh_eq ℓ']
      ring
    simp only [e3] at hβ
    exact hβ
  · dsimp only
    rw [← hξh_eq l, ← hξh_eq l']
    exact hA l l' hnot
  · dsimp only
    rw [← hξh_eq l', ← hdiff l, betaH_sub_left, hB l l' hnot, hA l l' hnot, sub_zero]
  · dsimp only
    rw [← hξh_eq l, ← hdiff l', betaH_sub_right, hC l l' hnot, hA l l' hnot, sub_zero]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
