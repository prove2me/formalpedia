-- Prove2me | solution 1 for PI.DvRows.local_pairing_perfect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:08.322901+00:00
-- url     : https://prove2.me/submissions/6a297549-7a10-48e3-93d1-164356f01ed6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pairing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LocalPairingPerfect
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_PI_DvRows_lidx_add_of_span_eq__d114b9139d51
import Theorems.Thm_P2M_PI_DvRows_vAdd_mul__c62e31a6c4e3
import Theorems.Thm_PI_DvRows_card_le_of_orth
import Theorems.Thm_PI_DvRows_den_of_locP
import Theorems.Thm_PI_DvRows_det_ne_zero_of_comb
import Theorems.Thm_PI_DvRows_h_smul_left
import Theorems.Thm_PI_DvRows_h_smul_right
import Theorems.Thm_PI_DvRows_lattice_finitely_generated
import Theorems.Thm_PI_DvRows_lattice_locally_free
import Theorems.Thm_PI_DvRows_lidx_span_act
import Theorems.Thm_PI_DvRows_lidx_zero_of_loc
import Theorems.Thm_PI_DvRows_linInd_left
import Theorems.Thm_PI_DvRows_mem_iff_vAdd_pos
import Theorems.Thm_PI_DvRows_vAdd_inv
import Theorems.Thm_PI_DvRows_vAdd_unit
import Theorems.Thm_PI_LatIdxDetW_lidx_antisymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.HermitianLatticesTheory
namespace PI.DvRows
theorem _root_.solution : LocalPairing := by
  intro K _ _ _ _ _ A e n h hyp U hU k d u z y hlin hspz hspu hzM hy hyΛ hspy w w' hww
  classical
  obtain ⟨hS, hP, hH, hC⟩ := hyp
  obtain ⟨hG, hn, hee, hnL, hmaj⟩ := hP
  haveI : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  set M := cutE A e A.L with hMdef
  set S := cutE A e A.L ⊓ U.restrictScalars (𝓞 K) with hSdef
  set Λ := lamSub A e h U with hΛdef
  set zf := Fin.append u z with hzf
  have hu : LinearIndependent K u := linInd_left u z hlin
  have hye : ∀ i, y i ∈ LinearMap.range e := fun i => (hyΛ i).1
  have hyU : ∀ i, ∀ x ∈ U, h (y i) x = 0 := fun i => (hyΛ i).2.1
  have hMfg : M.FG := Submodule.FG.of_le hG.2.1 inf_le_left
  have hSfg : S.FG := Submodule.FG.of_le hG.2.1 (inf_le_left.trans inf_le_left)
  have hΛfg : Λ.FG := lattice_finitely_generated K A e n h ⟨hS, ⟨hG, hn, hee, hnL, hmaj⟩, hH, hC⟩ U hU
  have hkU : Module.finrank K U = k := by
    rw [← hspu, finrank_span_eq_card hu, Fintype.card_fin]
  have hdimE : dimE A e = k + d := by
    unfold dimE
    rw [← hspz, finrank_span_eq_card hlin, Fintype.card_fin]
  have hdy : Module.finrank K (Submodule.span K (Set.range y)) = d := by
    rw [finrank_span_eq_card hy, Fintype.card_fin]

  have huM : ∀ i, u i ∈ M := fun i => by
    have := hzM (Fin.castAdd d i); simpa [hzf] using this
  have huU : ∀ i, u i ∈ U := fun i => by rw [← hspu]; exact Submodule.subset_span ⟨i, rfl⟩
  have hzM' : ∀ j, z j ∈ M := fun j => by
    have := hzM (Fin.natAdd k j); simpa [hzf] using this
  have hMe : ∀ x ∈ M, x ∈ LinearMap.range e := fun x hx => hx.2
  have hspanS : Submodule.span K (S : Set A.V) = U := by
    apply le_antisymm
    · exact Submodule.span_le.2 (fun x hx => hx.2)
    · rw [← hspu]
      exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨huM i, huU i⟩)
  have hspanM : Submodule.span K (M : Set A.V) = LinearMap.range e := by
    apply le_antisymm
    · exact Submodule.span_le.2 (fun x hx => hx.2)
    · rw [← hspz]
      exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span (hzM i))

  have F1 : ∀ x ∈ LinearMap.range e, (∀ i, h (y i) x = 0) → x ∈ U := by
    let Ψ : A.V →ₗ[K] (Fin d → K) := LinearMap.pi (fun i => h (y i))
    set X := LinearMap.range e ⊓ LinearMap.ker Ψ with hX
    have hUX : U ≤ X := fun x hx => ⟨hU hx, LinearMap.mem_ker.2 (funext fun i => hyU i x hx)⟩
    let bX := Module.finBasis K X
    let fam : Fin (Module.finrank K X) → A.V := fun i => (bX i : A.V)
    have hfam : LinearIndependent K fam :=
      bX.linearIndependent.map' X.subtype (Submodule.ker_subtype X)
    have hyle : Submodule.span K (Set.range y) ≤ LinearMap.range e :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hye i)
    have hcard := card_le_of_orth A e h hee hH (Submodule.span K (Set.range y)) hyle fam hfam
      (fun i => (bX i).2.1) (fun i v hv => by
        have hker : Submodule.span K (Set.range y) ≤ LinearMap.ker (h (fam i)) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨j, rfl⟩
          show h (fam i) (y j) = 0
          have h2 : Ψ (fam i) = 0 := LinearMap.mem_ker.1 (bX i).2.2
          have h3 : h (y j) (fam i) = 0 := congrFun h2 j
          rw [hH.1 (y j) (fam i), h3, star_zero]
        exact LinearMap.mem_ker.1 (hker hv))
    rw [hdy, hdimE] at hcard
    have hXU : X = U := (Submodule.eq_of_le_of_finrank_le hUX (by rw [hkU]; omega)).symm
    intro x hx hx0
    have : x ∈ X := ⟨hx, LinearMap.mem_ker.2 (funext fun i => hx0 i)⟩
    rwa [hXU] at this

  let Φ : A.V →ₗ[K] (Fin d → K) := LinearMap.pi (fun i => h (y i))
  have hΦ : ∀ x i, Φ x i = h (y i) x := fun _ _ => rfl
  have hΦO : ∀ (c : 𝓞 K) (x : A.V), Φ (c • x) = c • Φ x := fun c x => Φ.map_smul_of_tower c x
  set N : Submodule (𝓞 K) (Fin d → K) := M.map (Φ.restrictScalars (𝓞 K)) with hNdef
  have hNfg : N.FG := hMfg.map _
  have hΦU : ∀ x ∈ U, Φ x = 0 := fun x hx => funext fun i => hyU i x hx

  obtain ⟨r1, a, ha, hspa, haS, hSa⟩ := lattice_locally_free K A.V w S hSfg
  obtain ⟨r2, nb, hnb, hspn, hnbN, hNn⟩ := lattice_locally_free K (Fin d → K) w N hNfg
  have hr1 : r1 = k := by
    have := finrank_span_eq_card ha
    rw [hspa, hspanS, hkU, Fintype.card_fin] at this
    exact this.symm
  subst hr1

  have hΦz : LinearIndependent K (fun j => Φ (z j)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 : Φ (∑ j, c j • z j) = 0 := by rw [map_sum]; simpa [map_smul] using hc
    have h2 : ∑ j, c j • z j ∈ U := F1 _ (Submodule.sum_mem _ (fun j _ =>
      Submodule.smul_mem _ _ (hMe _ (hzM' j)))) (fun i => congrFun h1 i)
    rw [← hspu, Submodule.mem_span_range_iff_exists_fun] at h2
    obtain ⟨b, hb⟩ := h2
    have h3 := (Fintype.linearIndependent_iff.1 hlin) (Fin.append (fun i => -b i) c) (by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, hzf, neg_smul, Finset.sum_neg_distrib]
      rw [hb]; abel)
    intro j
    have := h3 (Fin.natAdd r1 j)
    simpa using this
  have hr2 : r2 = d := by
    apply le_antisymm
    · have := hnb.fintype_card_le_finrank
      simpa using this
    · have hle : Submodule.span K (Set.range fun j => Φ (z j)) ≤ Submodule.span K (Set.range nb) := by
        rw [hspn]
        refine Submodule.span_le.2 ?_
        rintro _ ⟨j, rfl⟩
        exact Submodule.subset_span (Submodule.mem_map_of_mem (hzM' j))
      have := Submodule.finrank_mono hle
      rwa [finrank_span_eq_card hΦz, finrank_span_eq_card hnb, Fintype.card_fin, Fintype.card_fin] at this
  subst hr2

  have hlift : ∀ j, ∃ m ∈ M, Φ m = nb j := fun j => by
    obtain ⟨m, hm, hmj⟩ := Submodule.mem_map.1 (hnbN j)
    exact ⟨m, hm, hmj⟩
  choose m hmM hmΦ using hlift
  set C0 : Matrix (Fin r2) (Fin r2) K := Matrix.of fun i j => h (y i) (m j) with hC0def
  have hC0 : C0.det ≠ 0 := by
    refine det_ne_zero_of_comb (fun i => (Pi.single i (1 : K) : Fin r2 → K)) nb C0 hnb (fun j => ?_)
    funext l
    rw [← hmΦ j]
    simp [C0, hΦ, Finset.sum_apply, Pi.single_apply]

  set am : Fin (r1 + r2) → A.V := Fin.append a m with ham
  have haU : ∀ i, a i ∈ U := fun i => (haS i).2
  have hamM : ∀ i, am i ∈ M := by
    intro i
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
    · simp only [ham, Fin.append_left]; exact (haS i').1
    · simp only [ham, Fin.append_right]; exact hmM i'
  have hamli : LinearIndependent K am := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    simp only [ham, Fin.append_left, Fin.append_right] at hg
    have h1 : ∑ j, g (Fin.natAdd r1 j) • nb j = 0 := by
      have := congrArg Φ hg
      rw [map_add, map_sum, map_sum, map_zero] at this
      simp only [map_smul, hΦU _ (haU _), smul_zero, Finset.sum_const_zero, zero_add, hmΦ] at this
      exact this
    have h2 := (Fintype.linearIndependent_iff.1 hnb) _ h1
    simp only [h2, zero_smul, Finset.sum_const_zero, add_zero] at hg
    have h3 := (Fintype.linearIndependent_iff.1 ha) _ hg
    intro i
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
    · exact h3 i'
    · exact h2 i'
  have hspam : Submodule.span K (Set.range am) = LinearMap.range e := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hMe _ (hamM i))
    · rw [finrank_span_eq_card hamli, Fintype.card_fin]
      have := hdimE; unfold dimE at this; omega

  have hcu : ∀ j, ∃ c : Fin r1 → K, ∑ i, c i • a i = u j := fun j => by
    have : u j ∈ Submodule.span K (Set.range a) := by rw [hspa, hspanS]; exact huU j
    exact (Submodule.mem_span_range_iff_exists_fun K).1 this
  choose T1f hT1 using hcu
  have hcz : ∀ j, ∃ c : Fin (r1 + r2) → K, ∑ i, c i • am i = z j := fun j => by
    have : z j ∈ Submodule.span K (Set.range am) := by rw [hspam]; exact hMe _ (hzM' j)
    exact (Submodule.mem_span_range_iff_exists_fun K).1 this
  choose Zf hZ using hcz
  set T1 : Matrix (Fin r1) (Fin r1) K := Matrix.of fun c j => T1f j c with hT1def
  set R : Matrix (Fin r1) (Fin r2) K := Matrix.of fun c j => Zf j (Fin.castAdd r2 c) with hRdef
  set Q : Matrix (Fin r2) (Fin r2) K := Matrix.of fun c j => Zf j (Fin.natAdd r1 c) with hQdef
  set P : Matrix (Fin (r1 + r2)) (Fin (r1 + r2)) K :=
    (Matrix.fromBlocks T1 R 0 Q).submatrix finSumFinEquiv.symm finSumFinEquiv.symm with hPdef
  have hPdet : P.det = T1.det * Q.det := by
    rw [hPdef, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  have hzfP : ∀ j, zf j = ∑ c, P c j • am c := by
    intro j
    refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · rw [Fin.sum_univ_add]
      simp [hzf, hPdef, ham, T1, Matrix.fromBlocks, hT1]
    · rw [Fin.sum_univ_add]
      simp only [hzf, Fin.append_right, hPdef, ham, Fin.append_left, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, R, Q, Matrix.of_apply]
      rw [← hZ j', Fin.sum_univ_add]
      simp [ham]
  have hPne : P.det ≠ 0 := det_ne_zero_of_comb am zf P hlin hzfP
  have hT1ne : T1.det ≠ 0 := by intro h0; apply hPne; rw [hPdet, h0, zero_mul]
  have hQne : Q.det ≠ 0 := by intro h0; apply hPne; rw [hPdet, h0, mul_zero]
  have huT : ∀ j, u j = ∑ c, T1 c j • a c := fun j => by rw [← hT1 j]; rfl

  have hCeq : (Matrix.of fun i j => h (y i) (z j)) = C0 * Q := by
    ext i j
    rw [Matrix.of_apply, ← hZ j, map_sum, Fin.sum_univ_add]
    simp only [ham, Fin.append_left, Fin.append_right, map_smul, smul_eq_mul,
      hyU i _ (haU _), mul_zero, Finset.sum_const_zero, zero_add, Matrix.mul_apply, C0, Q,
      Matrix.of_apply]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring

  have hC0u : IsUnit C0.det := isUnit_iff_ne_zero.2 hC0
  set G : Matrix (Fin r2) (Fin r2) K := Matrix.of fun i k => star (C0⁻¹ k i) with hGdef
  set ys : Fin r2 → A.V := fun k => ∑ i, G i k • y i with hysdef
  have hys_dual : ∀ k j, h (ys k) (m j) = if k = j then 1 else 0 := by
    intro k j
    have hinv := congrFun (congrFun (Matrix.nonsing_inv_mul C0 hC0u) k) j
    rw [Matrix.mul_apply, Matrix.one_apply] at hinv
    rw [← hinv, hysdef, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
    simp [G, C0]
  have hysU : ∀ k, ∀ x ∈ U, h (ys k) x = 0 := by
    intro k x hx
    rw [hysdef, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [map_smulₛₗ, LinearMap.smul_apply, hyU i x hx, smul_zero]
  have hyse : ∀ k, ys k ∈ LinearMap.range e := fun k =>
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hye i))
  have hGdet : star G.det = C0.det⁻¹ := by
    have hGmap : G = (starRingEnd K).mapMatrix (C0⁻¹).transpose := by
      ext i k; simp [G, starRingEnd_apply]
    rw [hGmap, ← RingHom.map_det, Matrix.det_transpose, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv', starRingEnd_apply, star_star]
  have hGne : G.det ≠ 0 := by
    intro h0
    have := hGdet
    rw [h0, star_zero] at this
    exact inv_ne_zero hC0 this.symm
  have hys_comb : ∀ (c : Fin r2 → K) j, h (∑ k, c k • ys k) (m j) = star (c j) := by
    intro c j
    rw [map_sum, LinearMap.sum_apply]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hys_dual, starRingEnd_apply]
    simp
  have hysli : LinearIndependent K ys := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have := hys_comb c j
    rw [hc, map_zero, LinearMap.zero_apply] at this
    have h2 : star (c j) = 0 := this.symm
    simpa using congrArg star h2
  have hspys : Submodule.span K (Set.range ys) = Submodule.span K (Set.range y) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.2 (by
        rintro _ ⟨k, rfl⟩
        exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)))
    · rw [finrank_span_eq_card hysli, finrank_span_eq_card hy]

  have hΛys : Λ ≤ Submodule.span (𝓞 K) (Set.range ys) := by
    intro x hx
    have hxK : x ∈ Submodule.span K (Set.range ys) := by
      rw [hspys, ← hspy]; exact Submodule.subset_span hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hxK
    have hcO : ∀ j, c j ∈ Set.range (algebraMap (𝓞 K) K) := by
      intro j
      have h1 := hx.2.2 (m j) (hmM j)
      rw [← hc, hys_comb] at h1
      obtain ⟨o, ho⟩ := h1
      obtain ⟨o', ho'⟩ := star_mem_range o
      exact ⟨o', by rw [ho', ho, star_star]⟩
    choose o ho using hcO
    rw [← hc]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    rw [← ho j, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

  have hMloc : M ≤ localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range am)) := by
    intro x hx
    have hΦx : Φ x ∈ N := Submodule.mem_map_of_mem (f := Φ.restrictScalars (𝓞 K)) hx
    obtain ⟨t, ht, hts⟩ := hNn (Φ x) hΦx
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hts
    set x1 := t • x - ∑ j, β j • m j with hx1
    have hx1M : x1 ∈ M := M.sub_mem (M.smul_mem t hx) (Submodule.sum_mem _ (fun j _ => M.smul_mem _ (hmM j)))
    have hΦx1 : Φ x1 = 0 := by
      rw [hx1, map_sub, map_sum, hΦO]
      simp only [hΦO, hmΦ]
      rw [hβ, sub_self]
    have hx1U : x1 ∈ U := F1 x1 (hMe _ hx1M) (fun i => congrFun hΦx1 i)
    obtain ⟨t', ht', ht'x⟩ := hSa x1 ⟨hx1M, hx1U⟩
    refine ⟨t' * t, fun hmem => (w.isPrime.mem_or_mem hmem).elim ht' ht, ?_⟩
    have hsub : Submodule.span (𝓞 K) (Set.range a) ≤ Submodule.span (𝓞 K) (Set.range am) :=
      Submodule.span_mono (by rintro _ ⟨c, rfl⟩; exact ⟨Fin.castAdd r2 c, by simp [ham]⟩)
    have heq : (t' * t) • x = t' • x1 + ∑ j, (t' * β j) • m j := by
      rw [hx1, smul_sub, mul_smul, Finset.smul_sum]
      simp only [mul_smul]
      abel
    rw [heq]
    refine Submodule.add_mem _ (hsub ht'x) (Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ ?_))
    exact Submodule.subset_span ⟨Fin.natAdd r1 j, by simp [ham]⟩

  have hspOK : ∀ {r : ℕ} (f : Fin r → A.V), Submodule.span K
      ((Submodule.span (𝓞 K) (Set.range f) : Submodule (𝓞 K) A.V) : Set A.V) = Submodule.span K (Set.range f) :=
    fun f => Submodule.span_span_of_tower (𝓞 K) K (Set.range f)
  have hfg : ∀ {r : ℕ} (f : Fin r → A.V), (Submodule.span (𝓞 K) (Set.range f)).FG :=
    fun f => Submodule.fg_span (Set.finite_range f)
  have hle_loc : ∀ (p : Ideal (𝓞 K)) [p.IsPrime] (X : Submodule (𝓞 K) A.V), X ≤ localization₂ p X :=
    fun p _ X x hx => ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact hx⟩

  have hzfeq : zf = fun j => ∑ c, P c j • am c := funext hzfP
  have hi : lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range zf)) M = -vAdd w P.det := by
    rw [lidx_add_of_span_eq' (K := K) w.asIdeal _ (Submodule.span (𝓞 K) (Set.range am)) M (hfg _) (hfg _) hMfg
      (by rw [hspOK, hspOK, hspz, hspam]) (by rw [hspOK, hspam, hspanM])]
    have h1 : lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range am)) M = 0 :=
      lidx_zero_of_loc w.asIdeal
        ((Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hamM c)).trans (hle_loc _ M)) hMloc
    have h2 : lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range zf)) (Submodule.span (𝓞 K) (Set.range am)) =
        -vAdd w P.det := by
      rw [PI.LatIdxDetW.lidx_antisymm, hzfeq, lidx_span_act w am hamli P hPne]
    rw [h1, h2, add_zero]

  have hii : lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range u)) S = -vAdd w T1.det := by
    rw [lidx_add_of_span_eq' (K := K) w.asIdeal _ (Submodule.span (𝓞 K) (Set.range a)) S (hfg _) (hfg _) hSfg
      (by rw [hspOK, hspOK, hspu, hspa, hspanS]) (by rw [hspOK, hspa])]
    have h1 : lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range a)) S = 0 :=
      lidx_zero_of_loc w.asIdeal
        ((Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact haS c)).trans (hle_loc _ S)) hSa
    have hueq : u = fun j => ∑ c, T1 c j • a c := funext huT
    have h2 : lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range u)) (Submodule.span (𝓞 K) (Set.range a)) =
        -vAdd w T1.det := by
      rw [PI.LatIdxDetW.lidx_antisymm, hueq, lidx_span_act w a ha T1 hT1ne]
    rw [h1, h2, add_zero]

  obtain ⟨T, hT, hTM⟩ := den_of_locP w hMfg hMloc
  have hintam : ∀ k, ∀ v ∈ Submodule.span (𝓞 K) (Set.range am), h (ys k) v ∈ Set.range (algebraMap (𝓞 K) K) := by
    intro k v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨c, rfl⟩ := hv
      refine Fin.addCases (fun c' => ?_) (fun c' => ?_) c
      · simp only [ham, Fin.append_left]
        rw [hysU k _ (haU c')]; exact ⟨0, map_zero _⟩
      · simp only [ham, Fin.append_right]
        rw [hys_dual]
        split_ifs
        · exact ⟨1, map_one _⟩
        · exact ⟨0, map_zero _⟩
    | zero => rw [map_zero]; exact ⟨0, map_zero _⟩
    | add v1 v2 _ _ h1 h2 =>
      obtain ⟨o1, ho1⟩ := h1; obtain ⟨o2, ho2⟩ := h2
      exact ⟨o1 + o2, by rw [map_add, map_add, ho1, ho2]⟩
    | smul c v _ h1 =>
      obtain ⟨o1, ho1⟩ := h1
      exact ⟨c * o1, by rw [h_smul_right, map_mul, ho1]⟩
  obtain ⟨s, hs⟩ := star_mem_range T
  have hss : star (algebraMap (𝓞 K) K s) = algebraMap (𝓞 K) K T := by rw [hs, star_star]
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hT
    have : algebraMap (𝓞 K) K T = 0 := by rw [← hss, map_zero, star_zero]
    rw [(IsFractionRing.injective (𝓞 K) K) (this.trans (map_zero _).symm)]
    exact w.asIdeal.zero_mem
  have hsw' : s ∉ w'.asIdeal := by
    intro hmem
    have := (mem_iff_vAdd_pos w' hs0).1 hmem
    rw [hww, hss, vAdd_unit w T hT] at this
    exact lt_irrefl _ this
  have hysΛ : Submodule.span (𝓞 K) (Set.range ys) ≤ localization₂ w'.asIdeal Λ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨s, hsw', Submodule.smul_of_tower_mem _ s (hyse k), fun x hx => ?_, fun x hx => ?_⟩
    · rw [h_smul_left, hysU k x hx, mul_zero]
    · rw [h_smul_left, hss, ← h_smul_right]
      exact hintam k _ (hTM x hx)
  have hiii : lidx w'.asIdeal (Submodule.span (𝓞 K) (Set.range y)) Λ = vAdd w' G.det := by
    rw [lidx_add_of_span_eq' (K := K) w'.asIdeal _ (Submodule.span (𝓞 K) (Set.range ys)) Λ (hfg _) (hfg _) hΛfg
      (by rw [hspOK, hspOK, hspys]) (by rw [hspOK, hspys, hspy])]
    have h1 : lidx w'.asIdeal (Submodule.span (𝓞 K) (Set.range ys)) Λ = 0 :=
      lidx_zero_of_loc w'.asIdeal hysΛ (hΛys.trans (hle_loc _ _))
    rw [h1, add_zero, hysdef, lidx_span_act w' y hy G hGne]

  have hdetC : (Matrix.of fun i j => h (y i) (z j)).det = C0.det * Q.det := by
    rw [hCeq, Matrix.det_mul]
  have hvG : vAdd w' G.det = -vAdd w C0.det := by
    rw [hww, hGdet, vAdd_inv]
  rw [hdetC, vAdd_mul' w hC0 hQne, hiii, hi, hii, hvG, hPdet, vAdd_mul' w hT1ne hQne]
  ring
end PI.DvRows
