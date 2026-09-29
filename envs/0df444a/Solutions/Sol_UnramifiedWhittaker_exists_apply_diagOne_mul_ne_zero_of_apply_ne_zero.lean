-- Prove2me | solution 1 for UnramifiedWhittaker.exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9088c86e-4479-5cf0-a8cc-003c598d391b

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Theorems.Thm_UnramifiedWhittaker_apply_mul_placeEmbed_diagZ_eq_mul_torusFactor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero

set_option autoImplicit false

open Matrix
p2m_open "IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm UnramifiedWhittaker P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker AdelicDock"

namespace UnramifiedWhittaker
p2m_export "UnramifiedWhittaker" "unipotent diagZ repSome repInf scalarPi placeEmbed apply_mul_placeEmbed_diagZ_eq_mul_torusFactor"
namespace C8P1
p2m_open "UnramifiedWhittaker"

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

noncomputable def cpt (v : HeightOneSpectrum (𝓞 F)) :
    GL (Fin 2) (AdeleRing (𝓞 F) F) →* GL (Fin 2) (v.adicCompletion F) :=
  (finComponent (𝓞 F) F v).comp (glFin (𝓞 F) F)

variable {F}

theorem cpt_apply (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) (i j : Fin 2) :
    ((cpt F v g : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v := rfl

theorem placeEmbed_eq (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin 2) (v.adicCompletion F)) :
    placeEmbed F v x = finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v x) := rfl

theorem cpt_finEmbed (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    cpt F v (finEmbed (𝓞 F) F k) = finComponent (𝓞 F) F v k := by
  show finComponent (𝓞 F) F v (glFin (𝓞 F) F (finEmbed (𝓞 F) F k)) = _
  rw [glFin_finEmbed]

@[scoped simp] theorem cpt_placeEmbed_self (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin 2) (v.adicCompletion F)) :
    cpt F v (placeEmbed F v x) = x := by
  rw [placeEmbed_eq, cpt_finEmbed, finComponent_localEmbed_self]

theorem cpt_placeEmbed_of_ne {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v)
    (x : GL (Fin 2) (v.adicCompletion F)) : cpt F w (placeEmbed F v x) = 1 := by
  rw [placeEmbed_eq, cpt_finEmbed, finComponent_localEmbed_of_ne (𝓞 F) F v x hw]

@[scoped simp] theorem glArch_placeEmbed (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin 2) (v.adicCompletion F)) :
    glArch (𝓞 F) F (placeEmbed F v x) = 1 := by
  rw [placeEmbed_eq, glArch_finEmbed]

theorem ext_of_glArch_of_cpt {g h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (harch : glArch (𝓞 F) F g = glArch (𝓞 F) F h) (hfin : ∀ w, cpt F w g = cpt F w h) : g = h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · have := congrArg
      (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) harch
    simpa only [glArch_apply] using this
  · ext w : 1
    have := congrArg
      (fun m : GL (Fin 2) (w.adicCompletion F) => (m : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j)
      (hfin w)
    simpa only [cpt_apply] using this

theorem mul_placeEmbed_comm {v : HeightOneSpectrum (𝓞 F)} {g : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hg : cpt F v g = 1) (x : GL (Fin 2) (v.adicCompletion F)) :
    g * placeEmbed F v x = placeEmbed F v x * g := by
  refine ext_of_glArch_of_cpt (by rw [map_mul, map_mul, glArch_placeEmbed, mul_one, one_mul]) fun w => ?_
  rw [map_mul, map_mul]
  by_cases hw : w = v
  · subst hw; rw [hg, one_mul, mul_one]
  · rw [cpt_placeEmbed_of_ne hw, one_mul, mul_one]

theorem one_entry_snd (w : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 w
      = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem cpt_eq_one_iff (w : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    cpt F w g = 1 ↔ ∀ i j : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 w =
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 w := by
  rw [Matrix.GeneralLinearGroup.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [cpt_apply, one_entry_snd, Units.val_one]

theorem mem_localLevelOne_top {v : HeightOneSpectrum (𝓞 F)} (k k' : GL (Fin 2) (v.adicCompletion F))
    (hkk' : k * k' = 1)
    (hk : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1)
    (hk' : ∀ i j, Valued.v ((k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1) :
    k ∈ localLevelOne (𝓞 F) F v ⊤ := by
  have aux : ∀ m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F), (∀ i j, Valued.v (m i j) ≤ 1) →
      IsLocalLevelOne (𝓞 F) F v ⊤ m := fun m hm =>
    { integral := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hm i j)
      lowerLeft := by rw [idealBound_top]; exact hm 1 0
      lowerRight := by
        rw [idealBound_top, ← HeightOneSpectrum.mem_adicCompletionIntegers]
        exact sub_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hm 1 1)) (one_mem _) }
  rw [mem_localLevelOne_iff, inv_eq_of_mul_eq_one_right hkk']
  exact ⟨aux _ hk, aux _ hk'⟩

theorem placeEmbed_mem_of_mem_localLevelOne {v : HeightOneSpectrum (𝓞 F)}
    {k : GL (Fin 2) (v.adicCompletion F)} (hk : k ∈ localLevelOne (𝓞 F) F v ⊤) :
    placeEmbed F v k ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [placeEmbed_eq, finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff]; exact hk
  · rw [mem_finiteAdelicGL2Subgroup_iff, glArch_placeEmbed]

section W

variable {S : Finset (HeightOneSpectrum (𝓞 F))} {W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}

theorem apply_mul_placeEmbed_of_mem_localLevelOne
    (hK : ∀ k : GL (Fin 2) (AdeleRing (𝓞 F) F),
      k ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F →
      (∀ v ∈ S, ∀ i j : Fin 2,
        ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
          ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * k) = W g)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ localLevelOne (𝓞 F) F v ⊤) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    W (g * placeEmbed F v k) = W g :=
  hK _ (placeEmbed_mem_of_mem_localLevelOne hk)
    (fun w hw => (cpt_eq_one_iff w _).mp (cpt_placeEmbed_of_ne (fun h : w = v => hv (h ▸ hw)) k)) g

end W

end UnramifiedWhittaker.C8P1
p2m_reactivate "P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker.C8P1"
p2m_reactivate "P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker"

namespace UnramifiedWhittaker
p2m_export "UnramifiedWhittaker" "unipotent diagZ repSome repInf scalarPi placeEmbed apply_mul_placeEmbed_diagZ_eq_mul_torusFactor"
namespace C8P1
p2m_open "UnramifiedWhittaker"

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem isLocalLevelOne_top_of_forall_mem {v : HeightOneSpectrum (𝓞 F)}
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers F) : IsLocalLevelOne (𝓞 F) F v ⊤ m where
  integral := hm
  lowerLeft := by
    rw [idealBound_top]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm 1 0)
  lowerRight := by
    rw [idealBound_top, ← HeightOneSpectrum.mem_adicCompletionIntegers]
    exact sub_mem (hm 1 1) (one_mem _)

theorem eventually_cpt_mem (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    ∀ᶠ w in Filter.cofinite, cpt F w g ∈ localLevelOne (𝓞 F) F w ⊤ := by
  have h1 : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 w ∈ w.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2).property
  have h2 : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j : Fin 2,
      (((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 w
        ∈ w.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      ((((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2).property
  filter_upwards [h1, h2] with w hw1 hw2
  rw [mem_localLevelOne_iff, ← map_inv]
  exact ⟨isLocalLevelOne_top_of_forall_mem fun i j => hw1 i j,
    isLocalLevelOne_top_of_forall_mem fun i j => hw2 i j⟩

theorem mem_finiteLevelOne_of_forall_finComponent {N : Ideal (𝓞 F)}
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hk : ∀ w, finComponent (𝓞 F) F w k ∈ localLevelOne (𝓞 F) F w N) :
    k ∈ finiteLevelOne (𝓞 F) F N := by
  have aux : ∀ m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F),
      (∀ w, IsLocalLevelOne (𝓞 F) F w N
        ((finComponent (𝓞 F) F w m : GL (Fin 2) (w.adicCompletion F)) : Matrix _ _ _)) →
      IsLevelOneMatrix (𝓞 F) F N (m : Matrix _ _ _) := fun m hm =>
    { integral := fun i j w => (hm w).integral i j
      lowerLeft := fun w => (hm w).lowerLeft
      lowerRight := fun w => by
        rw [coe_sub_apply, coe_one_apply]; exact (hm w).lowerRight }
  rw [mem_finiteLevelOne_iff]
  refine ⟨aux k fun w => ((mem_localLevelOne_iff _ _ _ _).mp (hk w)).1,
    aux k⁻¹ fun w => ?_⟩
  rw [map_inv]
  exact ((mem_localLevelOne_iff _ _ _ _).mp (hk w)).2

theorem finComponent_prod_localEmbed (c : ∀ w : HeightOneSpectrum (𝓞 F), GL (Fin 2) (w.adicCompletion F))
    (w : HeightOneSpectrum (𝓞 F)) :
    ∀ l : List (HeightOneSpectrum (𝓞 F)), l.Nodup →
      finComponent (𝓞 F) F w (l.map fun w' => localEmbed (𝓞 F) F w' (c w')).prod
        = if w ∈ l then c w else 1
  | [], _ => by simp
  | (a :: l), hl => by
    rw [List.map_cons, List.prod_cons, map_mul,
      finComponent_prod_localEmbed c w l (List.nodup_cons.mp hl).2]
    by_cases hwa : w = a
    · subst hwa
      rw [finComponent_localEmbed_self, if_neg (List.nodup_cons.mp hl).1, mul_one, if_pos (List.mem_cons_self)]
    · rw [finComponent_localEmbed_of_ne (𝓞 F) F a (c a) hwa, one_mul]
      by_cases hwl : w ∈ l
      · rw [if_pos hwl, if_pos (List.mem_cons_of_mem a hwl)]
      · rw [if_neg hwl, if_neg (by simp [hwa, hwl])]

section W

variable {S : Finset (HeightOneSpectrum (𝓞 F))} {W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}

theorem exists_apply_ne_zero_cpt_eq_one_off_finset
    (hK : ∀ k : GL (Fin 2) (AdeleRing (𝓞 F) F),
      k ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F →
      (∀ v ∈ S, ∀ i j : Fin 2,
        ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
          ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * k) = W g)
    {g : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hg : W g ≠ 0) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (g₁ : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W g₁ ≠ 0 ∧ ∀ w, w ∉ S → w ∉ T → cpt F w g₁ = 1 := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ w, w ∉ T → cpt F w g ∈ localLevelOne (𝓞 F) F w ⊤ :=
    ⟨(Filter.eventually_cofinite.mp (eventually_cpt_mem g)).toFinset, fun w hw => by
      by_contra h; exact hw (Set.Finite.mem_toFinset _ |>.mpr h)⟩

  set L : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
    ((S ∪ T).toList.map fun w' => localEmbed (𝓞 F) F w' (cpt F w' g)).prod with hL
  set k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) := (glFin (𝓞 F) F g)⁻¹ * L with hk
  have hLw : ∀ w, finComponent (𝓞 F) F w L = if w ∈ S ∪ T then cpt F w g else 1 := fun w => by
    rw [hL, finComponent_prod_localEmbed (fun w' => cpt F w' g) w _ (Finset.nodup_toList _)]
    simp only [Finset.mem_toList]
  have hkw : ∀ w, finComponent (𝓞 F) F w k = (cpt F w g)⁻¹ * (if w ∈ S ∪ T then cpt F w g else 1) :=
    fun w => by rw [hk, map_mul, map_inv, hLw]; rfl
  have hkmem : ∀ w, finComponent (𝓞 F) F w k ∈ localLevelOne (𝓞 F) F w ⊤ := fun w => by
    rw [hkw]
    split_ifs with h
    · rw [inv_mul_cancel]; exact one_mem _
    · rw [mul_one]; exact inv_mem (hT w fun h' => h (Finset.mem_union_right _ h'))
  refine ⟨T, g * finEmbed (𝓞 F) F k, ?_, fun w hwS hwT => ?_⟩
  · rw [hK _ (Subgroup.mem_inf.mpr ⟨(finEmbed_mem_levelOne_iff _ _ _).mpr
        (mem_finiteLevelOne_of_forall_finComponent hkmem),
        (mem_finiteAdelicGL2Subgroup_iff _ _).mpr (glArch_finEmbed _ _ _)⟩) (fun w hw => ?_)]
    · exact hg
    · rw [← cpt_eq_one_iff, cpt_finEmbed, hkw, if_pos (Finset.mem_union_left _ hw), inv_mul_cancel]
  · rw [map_mul, cpt_finEmbed, hkw, if_neg (by simp [hwS, hwT]), mul_one, mul_inv_cancel]

end W
p2m_reactivate "P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker.C8P1"

end UnramifiedWhittaker.C8P1
p2m_reactivate "P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker.C8P1"
p2m_reactivate "P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker.C8P1"

namespace UnramifiedWhittaker
p2m_export "UnramifiedWhittaker" "unipotent diagZ repSome repInf scalarPi placeEmbed apply_mul_placeEmbed_diagZ_eq_mul_torusFactor"
namespace C8P1
p2m_open "UnramifiedWhittaker"

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

noncomputable def lowerUnipotent (t : v.adicCompletion F) : GL (Fin 2) (v.adicCompletion F) :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; t, 1] (by simp [det_fin_two_of])

variable (v) in

noncomputable def swapGL : GL (Fin 2) (v.adicCompletion F) :=
  GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [det_fin_two_of])

noncomputable def diagGL (a d : v.adicCompletion F) (ha : a ≠ 0) (hd : d ≠ 0) :
    GL (Fin 2) (v.adicCompletion F) :=
  GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, d] (by simp [det_fin_two_of, ha, hd])

@[scoped simp] theorem val_lowerUnipotent (t : v.adicCompletion F) :
    ((lowerUnipotent t : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![1, 0; t, 1] := rfl
@[scoped simp] theorem val_swapGL :
    ((swapGL v : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![0, 1; 1, 0] := rfl
@[scoped simp] theorem val_diagGL (a d : v.adicCompletion F) (ha : a ≠ 0) (hd : d ≠ 0) :
    ((diagGL a d ha hd : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![a, 0; 0, d] := rfl
@[scoped simp] theorem val_unipotent (x : v.adicCompletion F) :
    ((unipotent x : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![1, x; 0, 1] := rfl
@[scoped simp] theorem val_scalarPi (π : v.adicCompletion F) (hπ : π ≠ 0) :
    ((scalarPi π hπ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![π, 0; 0, π] := rfl
@[scoped simp] theorem val_diagZ (π : v.adicCompletion F) (hπ : π ≠ 0) (m : ℤ) :
    ((diagZ π hπ m : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![π ^ m, 0; 0, 1] := rfl

theorem lowerUnipotent_mem {t : v.adicCompletion F} (ht : Valued.v t ≤ 1) :
    lowerUnipotent t ∈ localLevelOne (𝓞 F) F v ⊤ := by
  refine mem_localLevelOne_top _ (lowerUnipotent (-t)) ?_ ?_ ?_
  · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, val_lowerUnipotent, val_lowerUnipotent, Matrix.mul_fin_two, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp
  · intro i j; fin_cases i <;> fin_cases j <;> simp [ht]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, ht]

theorem unipotent_mem (r : v.adicCompletionIntegers F) :
    unipotent (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r)
      ∈ localLevelOne (𝓞 F) F v ⊤ := by
  have hr : Valued.v (r : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp r.2
  refine mem_localLevelOne_top _
    (unipotent (-(algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r))) ?_ ?_ ?_
  · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, val_unipotent, val_unipotent, Matrix.mul_fin_two, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hr]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, hr]

variable (v) in
theorem swapGL_mem : swapGL v ∈ localLevelOne (𝓞 F) F v ⊤ := by
  refine mem_localLevelOne_top _ (swapGL v) ?_ ?_ ?_
  · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, val_swapGL, Matrix.mul_fin_two, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp
  · intro i j; fin_cases i <;> fin_cases j <;> simp
  · intro i j; fin_cases i <;> fin_cases j <;> simp

theorem diagGL_mem {a d : v.adicCompletion F} (ha : Valued.v a = 1) (hd : Valued.v d = 1) :
    diagGL a d ((Valuation.ne_zero_iff _).mp (ha ▸ one_ne_zero)) ((Valuation.ne_zero_iff _).mp (hd ▸ one_ne_zero))
      ∈ localLevelOne (𝓞 F) F v ⊤ := by
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff _).mp (ha ▸ one_ne_zero)
  have hd0 : d ≠ 0 := (Valuation.ne_zero_iff _).mp (hd ▸ one_ne_zero)
  refine mem_localLevelOne_top _ (diagGL a⁻¹ d⁻¹ (inv_ne_zero ha0) (inv_ne_zero hd0)) ?_ ?_ ?_
  · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, val_diagGL, val_diagGL, Matrix.mul_fin_two, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp [ha0, hd0]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [ha, hd]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [map_inv₀, ha, hd]

theorem exists_eq_zpow_mul {π : v.adicCompletion F} (hπ : Valued.v π = WithZero.exp (-1 : ℤ))
    {t : v.adicCompletion F} (ht : t ≠ 0) :
    ∃ (a : ℤ) (u : v.adicCompletion F), Valued.v u = 1 ∧ t = π ^ a * u := by
  have hπ0 : π ≠ 0 := fun h => by rw [h, map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).mpr ht
  have hπa : Valued.v (π ^ (-WithZero.log (Valued.v t))) = Valued.v t := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, neg_mul_neg, mul_one, WithZero.exp_log hvt]
  refine ⟨-WithZero.log (Valued.v t), (π ^ (-WithZero.log (Valued.v t)))⁻¹ * t, ?_, ?_⟩
  · rw [map_mul, map_inv₀, hπa, inv_mul_cancel₀ hvt]
  · rw [mul_inv_cancel_left₀ (zpow_ne_zero _ hπ0)]

theorem det_coe_ne_zero (x : GL (Fin 2) (v.adicCompletion F)) :
    (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det x).ne_zero

theorem exists_mul_upper (x : GL (Fin 2) (v.adicCompletion F)) :
    ∃ k ∈ localLevelOne (𝓞 F) F v ⊤,
      ((x * k : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by
  obtain ⟨a, b, c, d, hx⟩ : ∃ a b c d : v.adicCompletion F,
      (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c ≠ 0 := by rw [← Matrix.det_fin_two_of, ← hx]; exact det_coe_ne_zero x
  rcases le_or_gt (Valued.v c) (Valued.v d) with hcd | hdc
  · have hd : d ≠ 0 := by
      rintro rfl
      rw [map_zero, le_zero_iff, Valuation.zero_iff] at hcd
      exact hdet (by rw [hcd]; ring)
    refine ⟨lowerUnipotent (-(c / d)), lowerUnipotent_mem ?_, ?_⟩
    · rw [Valuation.map_neg, map_div₀]
      exact div_le_one_of_le₀ hcd zero_le'
    · have h : d * (c / d) = c := by field_simp
      rw [Units.val_mul, hx, val_lowerUnipotent, Matrix.mul_fin_two]
      simp [h]
  · have hc : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hdc
      exact not_lt_zero hdc
    refine ⟨swapGL v * lowerUnipotent (-(d / c)), mul_mem (swapGL_mem v) (lowerUnipotent_mem ?_), ?_⟩
    · rw [Valuation.map_neg, map_div₀]
      exact div_le_one_of_le₀ hdc.le zero_le'
    · have h : c * (d / c) = d := by field_simp
      rw [← mul_assoc, Units.val_mul, Units.val_mul, hx, val_swapGL, val_lowerUnipotent, Matrix.mul_fin_two,
        Matrix.mul_fin_two]
      simp [h]

theorem exists_iwasawa {π : v.adicCompletion F} (hπv : Valued.v π = WithZero.exp (-1 : ℤ)) (hπ0 : π ≠ 0)
    (x : GL (Fin 2) (v.adicCompletion F)) :
    ∃ (ξ : v.adicCompletion F) (a c : ℤ) (k : GL (Fin 2) (v.adicCompletion F)),
      k ∈ localLevelOne (𝓞 F) F v ⊤ ∧
      x = unipotent ξ * diagGL (π ^ a) (π ^ c) (zpow_ne_zero a hπ0) (zpow_ne_zero c hπ0) * k := by
  obtain ⟨k₁, hk₁, h10⟩ := exists_mul_upper x
  obtain ⟨α, β, γ, δ, hy⟩ : ∃ α β γ δ : v.adicCompletion F,
      ((x * k₁ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
        = !![α, β; γ, δ] := ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hγ : γ = 0 := by rw [hy] at h10; simpa using h10
  have hdet : α * δ ≠ 0 := by
    have := det_coe_ne_zero (x * k₁)
    rw [hy, Matrix.det_fin_two_of, hγ, mul_zero, sub_zero] at this
    exact this
  obtain ⟨a, u₁, hu₁, hαu⟩ := exists_eq_zpow_mul hπv (left_ne_zero_of_mul hdet)
  obtain ⟨c, u₂, hu₂, hδu⟩ := exists_eq_zpow_mul hπv (right_ne_zero_of_mul hdet)
  have hδ : δ ≠ 0 := right_ne_zero_of_mul hdet
  have hu₁0 : u₁ ≠ 0 := (Valuation.ne_zero_iff _).mp (hu₁ ▸ one_ne_zero)
  have hu₂0 : u₂ ≠ 0 := (Valuation.ne_zero_iff _).mp (hu₂ ▸ one_ne_zero)
  refine ⟨β / δ, a, c, diagGL u₁ u₂ hu₁0 hu₂0 * k₁⁻¹, mul_mem (diagGL_mem hu₁ hu₂) (inv_mem hk₁), ?_⟩
  have hy' : x * k₁ = unipotent (β / δ) * diagGL (π ^ a) (π ^ c) (zpow_ne_zero a hπ0) (zpow_ne_zero c hπ0)
      * diagGL u₁ u₂ hu₁0 hu₂0 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [hy, Units.val_mul, Units.val_mul, val_unipotent, val_diagGL, val_diagGL, Matrix.mul_fin_two,
      Matrix.mul_fin_two]
    fin_cases i <;> fin_cases j
    · simp [hαu]
    · simp [hδu]; field_simp
    · simp [hγ]
    · simp [hδu]
  rw [← mul_assoc, ← hy', mul_assoc, mul_inv_cancel, mul_one]

theorem val_scalarPi_pow (π : v.adicCompletion F) (hπ : π ≠ 0) (n : ℕ) :
    ((scalarPi π hπ ^ n : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![π ^ n, 0; 0, π ^ n] := by
  induction n with
  | zero => rw [pow_zero, Units.val_one, pow_zero]; exact Matrix.one_fin_two
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, val_scalarPi, Matrix.mul_fin_two]
    simp [pow_succ]

theorem diagGL_mul_scalarPi_pow {π : v.adicCompletion F} (hπ0 : π ≠ 0) (a c : ℤ) :
    diagGL (π ^ a) (π ^ c) (zpow_ne_zero a hπ0) (zpow_ne_zero c hπ0) * scalarPi π hπ0 ^ (-c).toNat
      = scalarPi π hπ0 ^ c.toNat * diagZ π hπ0 (a - c) := by
  have hc : ((c.toNat : ℕ) : ℤ) - (((-c).toNat : ℕ) : ℤ) = c := Int.toNat_sub_toNat_neg c
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, val_scalarPi_pow, val_scalarPi_pow, val_diagGL, val_diagZ,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  have h00 : π ^ a * π ^ (-c).toNat = π ^ c.toNat * π ^ (a - c) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hπ0, ← zpow_add₀ hπ0]
    congr 1; omega
  have h11 : π ^ c * π ^ (-c).toNat = π ^ c.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hπ0]
    congr 1; omega
  fin_cases i <;> fin_cases j <;> simp [h00, h11]

theorem scalarPi_comm (π : v.adicCompletion F) (hπ : π ≠ 0) (y : GL (Fin 2) (v.adicCompletion F)) :
    scalarPi π hπ * y = y * scalarPi π hπ := by
  obtain ⟨a, b, c, d, hyx⟩ : ∃ a b c d : v.adicCompletion F,
      (y : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, hyx, val_scalarPi, Matrix.mul_fin_two, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

end UnramifiedWhittaker.C8P1
p2m_reactivate "P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker.C8P1"
p2m_reactivate "P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker.C8P1"

namespace UnramifiedWhittaker
p2m_export "UnramifiedWhittaker" "unipotent diagZ repSome repInf scalarPi placeEmbed apply_mul_placeEmbed_diagZ_eq_mul_torusFactor"
namespace C8P1
p2m_open "UnramifiedWhittaker"

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
  {W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}

theorem addChar_apply_ne_zero {A : Type*} [AddGroup A] (ψ : AddChar A ℂ) (x : A) : ψ x ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem apply_mul_placeEmbed_scalarPi_pow {π : v.adicCompletion F} (hπ : π ≠ 0) {om : ℂ}
    (hZ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * placeEmbed F v (scalarPi π hπ)) = om * W g)
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) (n : ℕ) :
    W (g * placeEmbed F v (scalarPi π hπ ^ n)) = om ^ n * W g := by
  induction n with
  | zero => rw [pow_zero, map_one, mul_one, pow_zero, one_mul]
  | succ n ih =>
    rw [pow_succ, map_mul, ← mul_assoc, hZ, ih, ← mul_assoc]
    congr 1; ring

theorem om_ne_zero {π : v.adicCompletion F} (hπ : π ≠ 0) {om : ℂ}
    (hZ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * placeEmbed F v (scalarPi π hπ)) = om * W g)
    {g : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hg : W g ≠ 0) : om ≠ 0 := by
  intro hom
  have := hZ (g * placeEmbed F v (scalarPi π hπ)⁻¹)
  rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one, hom, zero_mul] at this
  exact hg this

theorem apply_ne_zero_of_local {ψ : AddChar (v.adicCompletion F) ℂ} {ϖ : v.adicCompletionIntegers F}
    (hπ : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hπv : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) = WithZero.exp (-1 : ℤ))
    {lam om : ℂ} {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers F)
    (hψ0 : ∀ r : v.adicCompletionIntegers F,
      ψ (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers F,
      ψ (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r /
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) ≠ 1)
    (hN : ∀ (x : v.adicCompletion F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W (placeEmbed F v (unipotent x) * g) = ψ x * W g)
    (hKv : ∀ k ∈ localLevelOne (𝓞 F) F v ⊤, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      W (g * placeEmbed F v k) = W g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∑ i, W (g * placeEmbed F v (repSome
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b i))))) +
        W (g * placeEmbed F v (repInf
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      W (g * placeEmbed F v (scalarPi
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ)) = om * W g)
    {h : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hh : W h ≠ 0) :
    W (h * placeEmbed F v (cpt F v h)⁻¹) ≠ 0 := by
  set π := algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ with hπdef
  set h' := h * placeEmbed F v (cpt F v h)⁻¹ with hh'
  have hcpt : cpt F v h' = 1 := by rw [hh', map_mul, cpt_placeEmbed_self, mul_inv_cancel]
  have hdec : h = h' * placeEmbed F v (cpt F v h) := by
    rw [hh', mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  obtain ⟨ξ, a, c, k, hk, hx⟩ := exists_iwasawa hπv hπ (cpt F v h)
  have hom : om ≠ 0 := om_ne_zero hπ hZ hh

  have h1 : W (h' * placeEmbed F v (diagGL (π ^ a) (π ^ c) (zpow_ne_zero a hπ) (zpow_ne_zero c hπ))) ≠ 0 := by
    have e : W h = ψ ξ *
        W (h' * placeEmbed F v (diagGL (π ^ a) (π ^ c) (zpow_ne_zero a hπ) (zpow_ne_zero c hπ))) := by
      rw [hdec, hx, map_mul, map_mul, ← mul_assoc, hKv k hk, ← mul_assoc, mul_placeEmbed_comm hcpt,
        mul_assoc, hN]
    exact fun h0 => hh (by rw [e, h0, mul_zero])

  have h2 : W (h' * placeEmbed F v (scalarPi π hπ ^ c.toNat) * placeEmbed F v (diagZ π hπ (a - c))) ≠ 0 := by
    rw [mul_assoc, ← map_mul, ← diagGL_mul_scalarPi_pow hπ a c, map_mul, ← mul_assoc,
      apply_mul_placeEmbed_scalarPi_pow hπ hZ]
    exact mul_ne_zero (pow_ne_zero _ hom) h1

  have hcomm : ∀ y : GL (Fin 2) (v.adicCompletion F),
      h' * placeEmbed F v (scalarPi π hπ ^ c.toNat) * placeEmbed F v y
        = placeEmbed F v y * (h' * placeEmbed F v (scalarPi π hπ ^ c.toNat)) := fun y => by
    rw [mul_assoc, ← map_mul, (Commute.pow_left (scalarPi_comm π hπ y) c.toNat).eq, map_mul, ← mul_assoc,
      mul_placeEmbed_comm hcpt, mul_assoc]
  have hKu : ∀ (r : v.adicCompletionIntegers F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W (g * placeEmbed F v (unipotent
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r))) = W g :=
    fun r g => hKv _ (unipotent_mem r) g
  rw [UnramifiedWhittaker.apply_mul_placeEmbed_diagZ_eq_mul_torusFactor v hπ b hψ0 hψ1 hN hKu hT hZ hcomm
    (a - c)] at h2
  have h3 := left_ne_zero_of_mul h2
  rw [apply_mul_placeEmbed_scalarPi_pow hπ hZ] at h3
  exact right_ne_zero_of_mul h3

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

theorem exists_forall_cpt_eq_one
    (hstep : ∀ v ∉ S, ∀ h : GL (Fin 2) (AdeleRing (𝓞 F) F), W h ≠ 0 →
      W (h * placeEmbed F v (cpt F v h)⁻¹) ≠ 0)
    (U : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ h : GL (Fin 2) (AdeleRing (𝓞 F) F), W h ≠ 0 → (∀ w, w ∉ S → w ∉ U → cpt F w h = 1) →
      ∃ g₀ : GL (Fin 2) (AdeleRing (𝓞 F) F), W g₀ ≠ 0 ∧ ∀ w, w ∉ S → cpt F w g₀ = 1 := by
  induction U using Finset.induction_on with
  | empty => exact fun h hh htriv => ⟨h, hh, fun w hw => htriv w hw (Finset.notMem_empty w)⟩
  | insert v U hvU ih =>
    intro h hh htriv
    by_cases hvS : v ∈ S
    · exact ih h hh fun w hwS hwU => htriv w hwS (by
        rw [Finset.mem_insert]; rintro (rfl | h'); exacts [hwS hvS, hwU h'])
    · refine ih (h * placeEmbed F v (cpt F v h)⁻¹) (hstep v hvS h hh) fun w hwS hwU => ?_
      by_cases hwv : w = v
      · subst hwv; rw [map_mul, cpt_placeEmbed_self, mul_inv_cancel]
      · rw [map_mul, cpt_placeEmbed_of_ne hwv, mul_one]
        exact htriv w hwS (by simp [hwv, hwU])

end UnramifiedWhittaker.C8P1
p2m_reactivate "P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker.C8P1"
p2m_reactivate "P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.UnramifiedWhittaker.C8P1"

theorem solution
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), AddChar (v.adicCompletion F) ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v) ≠ 0)
    (hϖ : ∀ v ∉ S,
      Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) =
        WithZero.exp (-1 : ℤ))
    {I : HeightOneSpectrum (𝓞 F) → Type*} [∀ v, Fintype (I v)] [∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum (𝓞 F), I v → v.adicCompletionIntegers F)
    (lam om : HeightOneSpectrum (𝓞 F) → ℂ)
    (hψ0 : ∀ v ∉ S, ∀ r : v.adicCompletionIntegers F,
      ψ v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r) = 1)
    (hψ1 : ∀ v ∉ S, ∃ r : v.adicCompletionIntegers F,
      ψ v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r /
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) ≠ 1)
    (hN : ∀ v ∉ S, ∀ (x : v.adicCompletion F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W (placeEmbed F v (unipotent x) * g) = ψ v x * W g)
    (hT : ∀ v ∉ S, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∑ i, W (g * placeEmbed F v (repSome
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b v i))))) +
        W (g * placeEmbed F v (repInf
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        lam v * W g)
    (hZ : ∀ v ∉ S, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      W (g * placeEmbed F v (scalarPi
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        om v * W g)
    (hK : ∀ k : GL (Fin 2) (AdeleRing (𝓞 F) F),
      k ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F →
      (∀ v ∈ S, ∀ i j : Fin 2,
        ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
          ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * k) = W g)
    (hW : ∃ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W g ≠ 0) :
    ∃ (g₀ : GL (Fin 2) (AdeleRing (𝓞 F) F)) (a₀ : (AdeleRing (𝓞 F) F)ˣ),
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ i j : Fin 2,
        ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
          ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1) ∧
      W (diagOne a₀ * g₀) ≠ 0 := by
  classical
  obtain ⟨g, hg⟩ := hW
  obtain ⟨T, g₁, hg₁, hT₁⟩ := UnramifiedWhittaker.C8P1.exists_apply_ne_zero_cpt_eq_one_off_finset hK hg
  have hstep : ∀ v ∉ S, ∀ h : GL (Fin 2) (AdeleRing (𝓞 F) F), W h ≠ 0 →
      W (h * placeEmbed F v (UnramifiedWhittaker.C8P1.cpt F v h)⁻¹) ≠ 0 :=
    fun v hv h hh => UnramifiedWhittaker.C8P1.apply_ne_zero_of_local (hπ v) (hϖ v hv) (b v) (hψ0 v hv)
      (hψ1 v hv) (hN v hv)
      (fun k hk g => UnramifiedWhittaker.C8P1.apply_mul_placeEmbed_of_mem_localLevelOne hK hv hk g)
      (hT v hv) (hZ v hv) hh
  obtain ⟨g₀, hg₀, htriv⟩ :=
    UnramifiedWhittaker.C8P1.exists_forall_cpt_eq_one hstep T g₁ hg₁ fun w hwS hwT => hT₁ w hwS hwT
  refine ⟨g₀, 1, fun v hv => (UnramifiedWhittaker.C8P1.cpt_eq_one_iff v g₀).mp (htriv v hv),
    fun v _ => rfl, ?_⟩
  rwa [map_one, one_mul]

end S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero
end P2MW
export P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero (solution)
