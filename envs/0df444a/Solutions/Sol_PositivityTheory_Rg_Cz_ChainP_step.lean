-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ChainP.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:57.109435+00:00
-- url     : https://prove2.me/submissions/b1d7ae0d-4ba1-42f8-9ade-ca0b0d0c3c7a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChain
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_card1
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_card2
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_card3
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_xJ_comm
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_liftAdj
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_adjoin_commute
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_listSub_commute
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_listSub_comp
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_listSub_kill
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_qdet_comp
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one


section
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz
namespace ChainP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
private theorem pmap_lift_lemma {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {P : Type} (f : V →ₗ[ℂ] W) (X : Module.End ℂ V) (Y : Module.End ℂ W) (h : f ∘ₗ X = Y ∘ₗ f) :
    (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) ∘ₗ lift X =
      lift Y ∘ₗ (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) := by
  refine LinearMap.ext fun v => funext fun I => ?_
  simpa [lift] using LinearMap.congr_fun h (v I)
private theorem pmap_eAt_lemma_2 {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {P : Type} [DecidableEq P] (f : V →ₗ[ℂ] W) (p : P) (a b : Fin n) :
    (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) ∘ₗ eAt p a b =
      eAt p a b ∘ₗ (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) := by
  refine LinearMap.ext fun v => funext fun I => ?_
  by_cases h : I p = a <;> simp [eAt, h]
private theorem pmap_Om_lemma_3 {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {P : Type} [DecidableEq P] (f : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b, f ∘ₗ E a b = F a b ∘ₗ f) (p : P) :
    (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) ∘ₗ Om E p =
      Om F p ∘ₗ (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) := by
  refine LinearMap.ext fun v => ?_
  simp only [Om, LinearMap.comp_apply, LinearMap.sum_apply, map_sum, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hA := LinearMap.congr_fun (pmap_lift_lemma (P := P) f _ _ (h a b)) (eAt p b a v)
  have hB := LinearMap.congr_fun (pmap_eAt_lemma_2 f p b a) v
  simp only [LinearMap.comp_apply] at hA hB
  rw [hA, hB]
private theorem pmap_tE_lemma_4 {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {P : Type} [DecidableEq P] (S : Finset P) (f : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b, f ∘ₗ E a b = F a b ∘ₗ f) (a b : Fin n) :
    (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) ∘ₗ tE S E a b =
      tE S F a b ∘ₗ (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) := by
  refine LinearMap.ext fun v => ?_
  simp only [tE, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply, map_sum, map_add]
  have hA := LinearMap.congr_fun (pmap_lift_lemma (P := P) f _ _ (h a b)) v
  simp only [LinearMap.comp_apply] at hA
  rw [hA]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  have hB := LinearMap.congr_fun (pmap_eAt_lemma_2 f p a b) v
  simpa only [LinearMap.comp_apply] using hB
end ChainP
end PositivityTheory.Rg.Cz
end
end

set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.ChainP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.ChainP
theorem _root_.solution (hT : TensorGl) (hC : Curry) (hS : StepChar) (hH : Height) (hW : WallQuot)
    (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (l : Fin n → ℂ) (ℓ : M →ₗ[ℂ] ℂ)
    (hWh : IsWh E ℓ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (m : ℕ) (co : Fin (m + 1) → Fin n)
    (ih : ∃ g, Good E l ℓ top m (co ∘ Fin.castSucc) g) : ∃ g, Good E l ℓ top (m + 1) co g := by
  obtain ⟨g, hG⟩ := ih
  unfold Good at hG ⊢
  obtain ⟨hgA, hg0, hgj, hgq⟩ := hG
  obtain ⟨hE'gl, -, -, -⟩ := hT n M (Fin m) E hE Finset.univ
  set E' : Fin n → Fin n → Module.End ℂ (TV n M (Fin m)) := tE (Finset.univ : Finset (Fin m)) E with hEe
  have hgc : ∀ a b, Commute g (E' a b) := fun a b =>
    adjoin_commute _ _ (by rintro x ⟨j, rfl⟩; exact xJ_comm hT E hE m j a b) g hgA
  set ℓ' : TV n M (Fin m) →ₗ[ℂ] ℂ := ℓ ∘ₗ LinearMap.proj (fun _ : Fin m => top) ∘ₗ g with hℓe
  set l' : Fin n → ℂ := fun k =>
    l k + ((Finset.univ.filter fun p : Fin m => (co ∘ Fin.castSucc) p = k).card : ℂ) with hl'
  have hq' : ∀ u, ℓ' ∘ₗ qdet E' u = (∏ k, (u + l' k)) • ℓ' := by
    intro u
    rw [hgq u]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [hl']
    ring
  obtain ⟨N0, F0, hF0gl, -, hF0ch, hF0int, hN0⟩ := hW n (TV n M (Fin m)) Unit (fun _ => E')
    (fun _ => hE'gl) (fun τ τ' h => absurd (Subsingleton.elim τ τ') h) (fun _ => l') ℓ' (fun _ u => hq' u)
  have hFgl : GlRel (F0 ()) := hF0gl ()
  have hFch : HasChar (F0 ()) l' := hF0ch ()
  have hFint : ∀ a b, N0.mkQ ∘ₗ E' a b = F0 () a b ∘ₗ N0.mkQ := hF0int ()
  have hN0le : N0 ≤ LinearMap.ker ℓ' := by
    intro y hy
    have := (hN0 y).1 hy 1 (Subalgebra.one_mem _)
    simpa using this
  set ψ := N0.liftQ ℓ' hN0le with hψe
  have hψapp : ∀ z, ψ (N0.mkQ z) = ℓ' z := fun z => by
    rw [hψe]
    exact Submodule.liftQ_apply _ _ _
  obtain ⟨-, -, hWhm⟩ := hH n M E hE ℓ hWh top htop
  obtain ⟨ψs, hψ1, hψ2, hψs⟩ := hWhm m
  have hψWh : IsWh (F0 ()) ψ := by
    refine ⟨ψs, hψ1, hψ2, fun a b hab => ?_⟩
    apply Submodule.linearMap_qext N0
    refine LinearMap.ext fun y => ?_
    have hFy := LinearMap.congr_fun (hFint a b) y
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hFy ⊢
    rw [← hFy, hψapp, hψapp]
    have h1 := LinearMap.congr_fun (hψs a b hab) (g y)
    have h2 := LinearMap.congr_fun (hgc a b).eq y
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Module.End.mul_apply] at h1 h2
    simp only [hℓe, LinearMap.comp_apply]
    rw [h2]
    exact h1
  have hψ0 : ψ ≠ 0 := by
    intro h
    apply hg0
    refine LinearMap.ext fun y => ?_
    have := hψapp y
    rw [h] at this
    simpa using this.symm
  obtain ⟨-, hnv, -⟩ := hH n (TV n M (Fin m) ⧸ N0) (F0 ()) hFgl ψ hψWh top htop
  obtain ⟨hkill, hSq⟩ := hS n (TV n M (Fin m) ⧸ N0) (F0 ()) hFgl l' hFch
  set L := (List.ofFn l').erase (l' (co (Fin.last m))) with hL
  have hLlen : L.length = top := by
    simp only [hL]
    rw [List.length_erase_of_mem (by simp), List.length_ofFn]
    omega
  set Om' := Om E' (0 : Fin 1) with hOm'
  set OmF := Om (F0 ()) (0 : Fin 1) with hOmF
  set PE : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1)) :=
    (L.map fun r => Om' - algebraMap ℂ _ r).prod with hPE
  set PF : Module.End ℂ (TV n (TV n M (Fin m) ⧸ N0) (Fin 1)) :=
    (L.map fun r => OmF - algebraMap ℂ _ r).prod with hPF
  set Q : TV n (TV n M (Fin m)) (Fin 1) →ₗ[ℂ] TV n (TV n M (Fin m) ⧸ N0) (Fin 1) :=
    LinearMap.pi fun I : Fin 1 → Fin n => N0.mkQ ∘ₗ LinearMap.proj I with hQ
  have hQOm : Q ∘ₗ Om' = OmF ∘ₗ Q := pmap_Om_lemma_3 N0.mkQ E' (F0 ()) hFint 0
  have hQP : Q ∘ₗ PE = PF ∘ₗ Q := listSub_comp Q Om' OmF hQOm L
  have hQsurj : Function.Surjective Q := by
    intro y
    refine ⟨fun I => (N0.mkQ_surjective (y I)).choose, funext fun I => ?_⟩
    exact (N0.mkQ_surjective (y I)).choose_spec
  have hΦ : ∀ z, ℓ' (PE z (fun _ => top)) = ψ (PF (Q z) (fun _ => top)) := by
    intro z
    have h := LinearMap.congr_fun hQP z
    simp only [LinearMap.comp_apply] at h
    rw [← h]
    exact (hψapp (PE z fun _ => top)).symm
  obtain ⟨hcb, hctE, hccast, hcnat, -, -, -⟩ := hC n M E m 1
  have hnat : Fin.natAdd m (0 : Fin 1) = Fin.last m := Fin.ext (by simp)
  have hxJ0 : xJ E' (0 : Fin 1) = Om' := by
    simp [xJ, hOm']
  have hcurX : curF n M m 1 ∘ₗ xJ E (Fin.last m) = Om' ∘ₗ curF n M m 1 := by
    have := hcnat 0
    rw [hnat, hxJ0] at this
    exact this
  obtain ⟨g1, hg1A, hg1⟩ := liftAdj hC E m g hgA
  have hcurP : curF n M m 1 ∘ₗ (L.map fun r => xJ E (Fin.last m) -
      algebraMap ℂ (Module.End ℂ (TV n M (Fin (m + 1)))) r).prod = PE ∘ₗ curF n M m 1 :=
    listSub_comp _ _ _ hcurX L
  have hliftP : ∀ X : Module.End ℂ (TV n M (Fin m)), (∀ a b, Commute X (E' a b)) →
      ∀ w, PE (lift X w) = lift X (PE w) := by
    intro X hX w
    have h1 : Commute (lift X : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1))) Om' :=
      pmap_Om_lemma_3 (P := Fin 1) X E' E' (fun a b => (hX a b).eq) 0
    have h2 := LinearMap.congr_fun (listSub_commute Om' (lift X) h1.symm L).eq w
    simpa only [Module.End.mul_apply] using h2
  have happend : ∀ y : TV n M (Fin (m + 1)),
      y (fun _ => top) = curF n M m 1 y (fun _ => top) (fun _ => top) := by
    intro y
    simp only [curF, LinearMap.pi_apply, LinearMap.proj_apply]
    congr 1
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  have hφ : ∀ x, ℓ (((L.map fun r => xJ E (Fin.last m) -
      algebraMap ℂ (Module.End ℂ (TV n M (Fin (m + 1)))) r).prod * g1) x (fun _ => top)) =
      ℓ' (PE (curF n M m 1 x) (fun _ => top)) := by
    intro x
    have h1 := LinearMap.congr_fun hcurP (g1 x)
    have h2 := LinearMap.congr_fun hg1 x
    simp only [LinearMap.comp_apply] at h1 h2
    refine (congrArg ℓ (happend _)).trans ?_
    rw [Module.End.mul_apply, h1, h2, hliftP g hgc]
    rfl
  have hkill' : PF * (OmF - algebraMap ℂ _ (l' (co (Fin.last m)))) = 0 :=
    listSub_kill OmF l' (co (Fin.last m)) hkill
  have hlastkey : ∀ w, ℓ' (PE (Om' w) (fun _ => top)) =
      l' (co (Fin.last m)) • ℓ' (PE w (fun _ => top)) := by
    intro w
    have e1 : PE (Om' w) - l' (co (Fin.last m)) • PE w = PE (Om' w - l' (co (Fin.last m)) • w) := by
      rw [map_sub, map_smul]
    have e2 : Q (Om' w - l' (co (Fin.last m)) • w) =
        (OmF - algebraMap ℂ _ (l' (co (Fin.last m)))) (Q w) := by
      have := LinearMap.congr_fun hQOm w
      simp only [LinearMap.comp_apply] at this
      rw [map_sub, map_smul, this, LinearMap.sub_apply, Module.algebraMap_end_apply]
    have e3 : PF ((OmF - algebraMap ℂ _ (l' (co (Fin.last m)))) (Q w)) = 0 := by
      have := LinearMap.congr_fun hkill' (Q w)
      simpa only [Module.End.mul_apply, LinearMap.zero_apply] using this
    have e4 : ℓ' (PE (Om' w - l' (co (Fin.last m)) • w) (fun _ => top)) = 0 := by
      rw [hΦ, e2, e3]
      simp
    rw [← e1] at e4
    have e5 : (PE (Om' w) - l' (co (Fin.last m)) • PE w) (fun _ => top) =
        PE (Om' w) (fun _ => top) - l' (co (Fin.last m)) • PE w (fun _ => top) := rfl
    rw [e5, map_sub, map_smul, sub_eq_zero] at e4
    exact e4
  obtain ⟨hTFgl, hOmFc, -, -⟩ := hT n (TV n M (Fin m) ⧸ N0) (Fin 1) (F0 ()) hFgl Finset.univ
  have hPFtE : ∀ a b, PF ∘ₗ tE Finset.univ (F0 ()) a b = tE Finset.univ (F0 ()) a b ∘ₗ PF :=
    fun a b => (listSub_commute _ _ (hOmFc 0 (Finset.mem_univ _) a b) L).eq
  have hWinv : ∀ a b, ∀ w ∈ LinearMap.range PF, tE Finset.univ (F0 ()) a b w ∈ LinearMap.range PF := by
    rintro a b _ ⟨y, rfl⟩
    refine ⟨tE Finset.univ (F0 ()) a b y, ?_⟩
    have := LinearMap.congr_fun (hPFtE a b) y
    simpa only [LinearMap.comp_apply] using this
  have hOO := LinearMap.congr_fun (listSub_commute OmF OmF (Commute.refl _) L).eq
  have hWO : ∀ w ∈ LinearMap.range PF, OmF w ∈ LinearMap.range PF := by
    rintro _ ⟨y, rfl⟩
    refine ⟨OmF y, ?_⟩
    simpa only [Module.End.mul_apply] using hOO y
  have hWsc : ∀ y, OmF (PF y) = l' (co (Fin.last m)) • PF y := by
    intro y
    have h1 := LinearMap.congr_fun hkill' y
    have h2 := hOO y
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply, map_sub, map_smul,
      LinearMap.zero_apply] at h1 h2
    rw [← h2]
    exact sub_eq_zero.mp h1
  have hFW := hSq (LinearMap.range PF) (LinearMap.range PF)
    (fun a b => (tE Finset.univ (F0 ()) a b).restrict (hWinv a b)) LinearMap.id hWinv hWO (co (Fin.last m))
    Function.surjective_id (fun a b w => rfl) (fun w => by
      obtain ⟨_, y, rfl⟩ := w
      exact Subtype.ext (hWsc y))
  have hWchar : ∀ u y, qdet (tE Finset.univ (F0 ())) u (PF y) =
      (∏ k, (u + Function.update l' (co (Fin.last m)) (l' (co (Fin.last m)) + 1) k)) • PF y := by
    intro u y
    have hsub := LinearMap.congr_fun (qdet_comp (LinearMap.range PF).subtype
      (fun a b => (tE Finset.univ (F0 ()) a b).restrict (hWinv a b)) (tE Finset.univ (F0 ()))
      (fun a b => LinearMap.ext fun w => rfl) u) ⟨PF y, y, rfl⟩
    simp only [LinearMap.comp_apply] at hsub
    rw [hFW u] at hsub
    simpa using hsub.symm
  refine ⟨(L.map fun r => xJ E (Fin.last m) -
      algebraMap ℂ (Module.End ℂ (TV n M (Fin (m + 1)))) r).prod * g1, ?_, ?_, ?_, ?_⟩
  · refine Subalgebra.mul_mem _ (list_prod_mem ?_) hg1A
    intro x hx
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
    exact Subalgebra.sub_mem _ (Algebra.subset_adjoin ⟨Fin.last m, rfl⟩) (Subalgebra.algebraMap_mem _ r)
  · intro h0
    apply hnv hψ0 L hLlen
    refine LinearMap.ext fun v => ?_
    obtain ⟨z, rfl⟩ := hQsurj v
    obtain ⟨x, rfl⟩ := hcb.2 z
    have := LinearMap.congr_fun h0 x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.proj_apply] at this ⊢
    rw [← hΦ, ← hφ]
    exact this
  · intro j
    cases j using Fin.lastCases with
    | last =>
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.proj_apply]
      rw [hφ, hφ]
      have hx := LinearMap.congr_fun hcurX x
      simp only [LinearMap.comp_apply] at hx
      rw [hx, hlastkey, card2]
    | cast i =>
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.proj_apply]
      rw [hφ, hφ]
      have hx := LinearMap.congr_fun (hccast i) x
      simp only [LinearMap.comp_apply] at hx
      rw [card1, show Fin.castSucc i = Fin.castAdd 1 i from rfl, hx,
        hliftP (xJ E i) (fun a b => xJ_comm hT E hE m i a b)]
      have hj := LinearMap.congr_fun (hgj i) (PE (curF n M m 1 x) (fun _ => top))
      simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hj
      exact hj
  · intro u
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.proj_apply]
    rw [hφ, hφ]
    have hq1 := LinearMap.congr_fun (qdet_comp (curF n M m 1) _ _ hctE u) x
    simp only [LinearMap.comp_apply] at hq1
    rw [hq1, hΦ, hΦ]
    have hq2 := LinearMap.congr_fun (qdet_comp Q _ _
      (pmap_tE_lemma_4 Finset.univ N0.mkQ E' (F0 ()) hFint) u) (curF n M m 1 x)
    simp only [LinearMap.comp_apply] at hq2
    rw [hq2]
    have hq3 := LinearMap.congr_fun (qdet_comp PF _ _ hPFtE u) (Q (curF n M m 1 x))
    simp only [LinearMap.comp_apply] at hq3
    rw [hq3, hWchar, Pi.smul_apply, map_smul]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [card3]
    by_cases hk : k = co (Fin.last m)
    · subst hk
      simp only [Function.update_self, if_true, hl']
      push_cast
      ring
    · rw [Function.update_of_ne hk, if_neg (Ne.symm hk)]
      simp only [hl']
      push_cast
      ring
end PositivityTheory.Rg.Cz.ChainP
